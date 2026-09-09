import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2887`: `x = ((x ◇ (y ◇ z)) ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pyx_x_pxy_Equation2887 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2887 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2887.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X2 X3)) X2)) (M.op (M.op X0 (M.op X2 X3)) X2)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 (M.op X2 X3)) X2) X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X1 X2)) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X1 X2)) X1 X2
       have i₂ := eq9 X0 (M.op X1 X2) X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq64 (σ X0)
       grind)
    | exact superpose eq64 eq15
    | exact resolve eq15 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq67 X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq67
    | exact resolve eq67 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq67
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq108 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X2 X3)) X2)) = (M.op (M.op X1 (M.op X0 (M.op X2 X3))) (M.op X0 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63 X1 (M.op X0 (M.op X2 X3)) X2 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X2 (M.op X0 (M.op (M.op X1 X3) X4))) (M.op X0 (M.op (M.op X1 X3) X4))) = (M.op (M.op X2 (M.op (M.op (M.op X0 X1) X1) X5)) (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq63 X0 (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X1 X2) X3
       have i₂ := eq63 X0 X1 X2 X3
       grind)
    | exact superpose eq63 eq63
    | exact resolve eq63 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 (M.op X1 X2) x
       have i₂ := eq63 X0 X1 X2 x
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op (M.op (M.op (M.op X0 X1) X1) X1) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 (M.op (M.op X1 X2) X3)) X1 X2
       have i₂ := eq63 X0 X1 X2 X3
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X0 (M.op (M.op X1 X3) X4))) (M.op X0 (M.op (M.op X1 X3) X4))) = (M.op (M.op X2 (M.op X0 X1)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq113 X0 X1 X2 X3 X4 x
       have i₂ := eq63 X2 (M.op X0 X1) X1 x
       grind)
    | exact superpose eq63 eq113
    | exact resolve eq113 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq381 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq78 X1
       grind)
    | exact superpose eq78 eq85
    | (have j0 := eq85 X0 X1
       grind)
    | exact resolve eq85 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq382 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq381 X0 X1
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq381
    | (have j0 := eq381 X0 X1
       grind)
    | exact resolve eq381 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq516 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq382 x y
       grind)
    | exact superpose eq382 eq16
    | (have j1 := eq382 x y
       grind)
    | exact resolve eq16 eq382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq876 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op X0 (M.op (M.op X1 X4) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq116 X0 X1 X2 X3
       have i₂ := eq116 X0 X1 X4 X5
       grind)
    | exact superpose eq116 eq116
    | exact resolve eq116 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq3219 : ∀ X0 X1 X2 X5 X6 : G, (M.op X1 X0) = (M.op X1 (M.op (M.op (M.op X0 X2) X5) X6)) := by
    intro X0 X1 X2 X5 X6
    first
    | (have i₁ := eq876 X1 (M.op X0 X2) (M.op (M.op X2 (M.op x x)) x) (M.op (M.op X2 (M.op x x)) x) X5 X6
       have i₂ := eq62 X2 X0 x x
       grind)
    | exact superpose eq62 eq876
    | exact resolve eq876 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq5291 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq516
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq516
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq516
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq516
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq516 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq5292 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x x) = (M.op y y) := by grind
  clear eq5291
  have eq14045 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X0 X1)) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op (M.op X0 (M.op (M.op X1 X3) X4)) (M.op X1 X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq118 X0 X1 X2 X3 X4
       have i₂ := eq108 X0 X2 (M.op X1 X3) X4
       grind)
    | exact superpose eq108 eq118
    | exact resolve eq118 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq118
  have eq14046 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X0 X1)) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14045 X0 X1 X2 x x
       have i₂ := eq63 X0 X1 x x
       grind)
    | exact superpose eq63 eq14045
    | exact resolve eq14045 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq14045
  have eq14637 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op X1 X2) X2)) (M.op (M.op X1 X2) X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq115 X0 (M.op X1 X2) X3
       have i₂ := eq14046 X1 X2 X0
       grind)
    | exact superpose eq14046 eq115
    | exact resolve eq115 eq14046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq14046
  have eq36697 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op X1 X2) X3)) (M.op (M.op X1 X4) X5)) = X0 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq14637 X0 X1 X4 X5
       have i₂ := eq876 (M.op X0 X1) X1 X4 X4 X2 X3
       grind)
    | (have i₁ := eq14637 X0 X1 X4 X5
       have i₂ := eq876 (M.op X0 X1) X1 X2 X3 X4 X4
       grind)
    | exact superpose eq876 eq14637
    | exact resolve eq14637 eq876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876 eq14637
  have eq362607 : (M.op y y) = (τ (σ (M.op x x))) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq5292
       grind)
    | exact superpose eq5292 eq10
    | exact resolve eq10 eq5292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5292
  have eq362764 : (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq362607
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq362607
    | exact resolve eq362607 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362607
  have eq362765 : (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq362764
  have eq362980 : ∀ X0 X1 X2 : G, (M.op X0 y) = (M.op X0 (M.op (M.op (M.op x x) X1) X2)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3219 y X0 y X1 X2
       have i₂ := eq362765
       grind)
    | exact superpose eq362765 eq3219
    | exact resolve eq3219 eq362765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq363134 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq362980 X0 x x
       have i₂ := eq3219 x X0 x x x
       grind)
    | exact superpose eq3219 eq362980
    | exact resolve eq362980 eq3219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3219 eq362980
  have eq363869 : (M.op x x) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq362765
       have i₂ := eq363134 y
       grind)
    | exact superpose eq363134 eq362765
    | exact resolve eq362765 eq363134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362765 eq363134
  have eq363872 : (M.op x x) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq363869
  have eq364119 : ∀ X0 X1 X2 X3 : G, y = (M.op (M.op (M.op x x) (M.op (M.op x X0) X1)) (M.op (M.op x X2) X3)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq36697 y x X0 X1 X2 X3
       have i₂ := eq363872
       grind)
    | exact superpose eq363872 eq36697
    | exact resolve eq36697 eq363872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363872
  have eq364168 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq364119 x x x x
       have i₂ := eq36697 x x x x x x
       grind)
    | exact superpose eq36697 eq364119
    | exact resolve eq364119 eq36697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36697 eq364119
  have eq364169 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq364168
  have eq364229 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq364169
       grind)
    | exact superpose eq364169 eq10
    | exact resolve eq10 eq364169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364169
  have eq364367 : x = y ∨ x = y := by
    first
    | (have i₁ := eq364229
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq364229
    | exact resolve eq364229 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364229
  have eq364368 : x = y := by grind
  clear eq364367
  have eq364382 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq364368
       grind)
    | exact superpose eq364368 eq16
    | exact resolve eq16 eq364368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364368
  have eq364383 : False := by grind
  exact eq364383

/-- `Equation3714`: `x ◇ y = (x ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_pyx_pxy_Equation3714 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3714 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3714.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) (M.op X1 X0)) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq19 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq20 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (k X0 X0) (M.op X1 X0)) := by
    intro X0 X1
    grind
  have eq21 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq22 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq10
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq57 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (k X0 X0)) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq20
    | exact resolve eq20 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) := by
    intro X0
    grind
  have eq61 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) (k X0 X0)) := by
    intro X0
    grind
  clear eq59
  have eq98 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq18
    | (have j0 := eq18 X1 (σ X0)
       grind)
    | exact resolve eq18 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 : G, (k X1 X1) ≠ (k X1 X1) ∨ (M.op (k X1 X1) X0) = (k X0 (k X1 X1)) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (k X1 X1)
       have i₂ := eq61 X1
       grind)
    | exact superpose eq61 eq18
    | (have j0 := eq18 X0 (k X1 X1)
       grind)
    | (have r₁ := eq18 X0 (k X0 X0)
       have r₂ := eq61 X0
       grind)
    | exact resolve eq18 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq101 : ∀ X0 X1 : G, (M.op (k X1 X1) X0) = (k X0 (k X1 X1)) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq100 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq108 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19 (σ x) (σ y)
       grind)
    | exact superpose eq19 eq16
    | (have j1 := eq19 (k (σ y) (σ y)) (σ y)
       grind)
    | (have r₁ := eq16
       have r₂ := eq19 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq19 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq108
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq108
    | exact resolve eq108 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq112 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq109
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq109
    | exact resolve eq109 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq305 : ∀ X0 X1 : G, (M.op (σ (k X0 X0)) X1) = (k X1 (σ (k X0 X0))) ∨ (σ (k X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq101 X0 (σ X1)
       have i₂ := eq15 X1 X1
       grind)
    | exact superpose eq15 eq101
    | exact resolve eq101 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306 : ∀ X0 X1 : G, (M.op (τ (k X0 X0)) X1) = (k X1 (τ (k X0 X0))) ∨ (τ (k X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq101 X0 (τ X0)
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq101
    | exact resolve eq101 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq315 : ∀ X0 X1 : G, (M.op X0 (k X1 X1)) = (M.op (k X0 X0) (k X0 (k X1 X1))) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 (k X1 X1)
       have i₂ := eq101 X0 X1
       grind)
    | exact superpose eq101 eq20
    | (have j1 := eq101 X0 X1
       grind)
    | exact resolve eq20 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1168 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq112
       have i₂ := eq19 x y
       grind)
    | exact superpose eq19 eq112
    | (have j1 := eq19 (k y y) y
       grind)
    | (have r₁ := eq112
       have r₂ := eq19 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq112
       have r₂ := eq19 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq112 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq1169 : x = y ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq1168
  have eq1170 : (σ (M.op y y)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1169
       grind)
    | exact superpose eq1169 eq16
    | exact resolve eq16 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169
  have eq1171 : (k (σ y) (σ y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq1170
  have eq1172 : (k (σ y) (σ y)) ≠ (σ (k y y)) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq1171
  have eq1173 : y = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have r₁ := eq1172
       have r₂ := eq15 y y
       grind)
    | exact resolve eq1172 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172
  have eq1185 : ∀ X0 : G, (σ x) = (σ y) ∨ y = X0 ∨ (M.op y X0) = (k X0 y) ∨ (σ y) = (σ (k y y)) := by
    intro X0
    first
    | (have i₁ := eq101 X0 y
       have i₂ := eq1173
       grind)
    | exact superpose eq1173 eq101
    | exact resolve eq101 eq1173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1186 : ∀ X0 : G, (M.op (σ y) X0) = (k X0 (σ y)) ∨ (σ y) = X0 ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by
    intro X0
    first
    | (have i₁ := eq305 y x
       have i₂ := eq1173
       grind)
    | exact superpose eq1173 eq305
    | (have j0 := eq305 y (σ y)
       grind)
    | exact resolve eq305 eq1173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1173
  have eq1193 : ∀ X0 : G, (M.op (σ y) X0) = (k X0 (σ y)) ∨ (σ y) = X0 ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq1186 X0
       have j1 := eq98 y X0
       grind)
    | (have r₁ := eq1186 (σ (k y y))
       have r₂ := eq98 y x
       grind)
    | (have r₁ := eq1186 X0
       have r₂ := eq98 y x
       grind)
    | exact resolve eq1186 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq1186
  have eq1200 : ∀ X0 : G, (k X0 (σ y)) = (k (σ y) X0) ∨ (k X0 X0) = X0 ∨ (σ y) = X0 ∨ (σ y) = X0 ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq19 (σ y) X0
       have i₂ := eq1193 X0
       grind)
    | exact superpose eq1193 eq19
    | (have j0 := eq19 (k X0 X0) X0
       have j1 := eq1193 X0
       grind)
    | exact resolve eq19 eq1193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1201 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ y) = X0 ∨ (M.op X0 (σ y)) = (M.op (k X0 X0) (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq20 X0 (σ y)
       have i₂ := eq1193 X0
       grind)
    | exact superpose eq1193 eq20
    | (have j1 := eq1193 (σ x)
       grind)
    | exact resolve eq20 eq1193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1193
  have eq1209 : ∀ X0 : G, (σ x) = (σ y) ∨ (k X0 X0) = X0 ∨ (σ y) = X0 ∨ (k X0 (σ y)) = (k (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq1200 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200
  have eq2389 : ∀ X0 : G, x = (τ (σ y)) ∨ y = X0 ∨ (M.op y X0) = (k X0 y) ∨ (σ y) = (σ (k y y)) := by
    intro X0
    first
    | (have i₁ := eq10 x
       have i₂ := eq1185 X0
       grind)
    | exact superpose eq1185 eq10
    | (have j1 := eq1185 X0
       grind)
    | exact resolve eq10 eq1185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185
  have eq2427 : ∀ X0 : G, x = y ∨ y = X0 ∨ (M.op y X0) = (k X0 y) ∨ (σ y) = (σ (k y y)) := by
    intro X0
    first
    | (have i₁ := eq2389 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2389
    | (have j0 := eq2389 X0
       grind)
    | exact resolve eq2389 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2389
  have eq2433 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op (σ y) (σ y)) ∨ y = X0 ∨ (M.op y X0) = (k X0 y) ∨ (σ y) = (σ (k y y)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq2427 X0
       grind)
    | exact superpose eq2427 eq16
    | (have j1 := eq2427 X0
       grind)
    | exact resolve eq16 eq2427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2427
  have eq2436 : ∀ X0 : G, (k (σ y) (σ y)) ≠ (σ (M.op y y)) ∨ y = X0 ∨ (M.op y X0) = (k X0 y) ∨ (σ y) = (σ (k y y)) := by
    intro X0
    grind
  clear eq2433
  have eq2437 : ∀ X0 : G, (k (σ y) (σ y)) ≠ (σ (k y y)) ∨ y = X0 ∨ (M.op y X0) = (k X0 y) ∨ (σ y) = (σ (k y y)) := by
    intro X0
    grind
  clear eq2436
  have eq2438 : ∀ X0 : G, (M.op y X0) = (k X0 y) ∨ y = X0 ∨ (σ y) = (σ (k y y)) := by
    intro X0
    first
    | (have j0 := eq2437 X0
       grind)
    | (have r₁ := eq2437 X0
       have r₂ := eq15 y y
       grind)
    | exact resolve eq2437 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2437
  have eq2453 : ∀ X0 : G, (σ y) = (σ (k y y)) ∨ (σ X0) = y ∨ (M.op (σ X0) y) = (M.op (σ (k X0 X0)) (k (σ X0) y)) := by
    intro X0
    first
    | (have i₁ := eq57 X0 y
       have i₂ := eq2438 (σ X0)
       grind)
    | exact superpose eq2438 eq57
    | (have j1 := eq2438 (σ X0)
       grind)
    | exact resolve eq57 eq2438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq2438
  have eq2530 : ∀ X0 : G, x = (τ (σ y)) ∨ (σ y) = X0 ∨ (M.op X0 (σ y)) = (M.op (k X0 X0) (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq10 x
       have i₂ := eq1201 X0
       grind)
    | exact superpose eq1201 eq10
    | (have j1 := eq1201 X0
       grind)
    | exact resolve eq10 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201
  have eq2569 : ∀ X0 : G, x = y ∨ (σ y) = X0 ∨ (M.op X0 (σ y)) = (M.op (k X0 X0) (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq2530 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2530
    | (have j0 := eq2530 X0
       grind)
    | exact resolve eq2530 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2530
  have eq2576 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = X0 ∨ (M.op X0 (σ y)) = (M.op (k X0 X0) (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq2569 X0
       grind)
    | exact superpose eq2569 eq16
    | (have j1 := eq2569 X0
       grind)
    | exact resolve eq16 eq2569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2569
  have eq2577 : ∀ X0 : G, (k (σ y) (σ y)) ≠ (σ (M.op y y)) ∨ (σ y) = X0 ∨ (M.op X0 (σ y)) = (M.op (k X0 X0) (k X0 (σ y))) := by
    intro X0
    grind
  clear eq2576
  have eq2578 : ∀ X0 : G, (k (σ y) (σ y)) ≠ (σ (k y y)) ∨ (σ y) = X0 ∨ (M.op X0 (σ y)) = (M.op (k X0 X0) (k X0 (σ y))) := by
    intro X0
    grind
  clear eq2577
  have eq2579 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (k X0 X0) (k X0 (σ y))) ∨ (σ y) = X0 := by
    intro X0
    first
    | (have j0 := eq2578 X0
       grind)
    | (have r₁ := eq2578 X0
       have r₂ := eq15 y y
       grind)
    | exact resolve eq2578 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2578
  have eq2581 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (M.op (σ (k X0 X0)) (k (σ X0) (σ y))) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq2579 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq2579
    | (have j0 := eq2579 (σ X0)
       grind)
    | exact resolve eq2579 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2579
  have eq2597 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (M.op (σ (k X0 X0)) (σ (k X0 y))) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq2581 X0
       have i₂ := eq15 X0 y
       grind)
    | exact superpose eq15 eq2581
    | (have j0 := eq2581 X0
       grind)
    | exact resolve eq2581 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2581
  have eq4707 : ∀ X0 : G, x = (τ (σ y)) ∨ (k X0 X0) = X0 ∨ (σ y) = X0 ∨ (k X0 (σ y)) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq10 x
       have i₂ := eq1209 X0
       grind)
    | exact superpose eq1209 eq10
    | (have j1 := eq1209 X0
       grind)
    | exact resolve eq10 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209
  have eq4749 : ∀ X0 : G, x = y ∨ (k X0 X0) = X0 ∨ (σ y) = X0 ∨ (k X0 (σ y)) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq4707 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq4707
    | (have j0 := eq4707 X0
       grind)
    | exact resolve eq4707 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4707
  have eq4760 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op (σ y) (σ y)) ∨ (k X0 X0) = X0 ∨ (σ y) = X0 ∨ (k X0 (σ y)) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq4749 X0
       grind)
    | exact superpose eq4749 eq16
    | (have j1 := eq4749 X0
       grind)
    | exact resolve eq16 eq4749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4749
  have eq4761 : ∀ X0 : G, (k (σ y) (σ y)) ≠ (σ (M.op y y)) ∨ (k X0 X0) = X0 ∨ (σ y) = X0 ∨ (k X0 (σ y)) = (k (σ y) X0) := by
    intro X0
    grind
  clear eq4760
  have eq4762 : ∀ X0 : G, (k (σ y) (σ y)) ≠ (σ (k y y)) ∨ (k X0 X0) = X0 ∨ (σ y) = X0 ∨ (k X0 (σ y)) = (k (σ y) X0) := by
    intro X0
    grind
  clear eq4761
  have eq4763 : ∀ X0 : G, (k X0 X0) = X0 ∨ (σ y) = X0 ∨ (k X0 (σ y)) = (k (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq4762 X0
       grind)
    | (have r₁ := eq4762 X0
       have r₂ := eq15 y y
       grind)
    | exact resolve eq4762 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4762
  have eq4766 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (σ y) ∨ (k (σ X0) (σ y)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4763 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq4763
    | (have j0 := eq4763 (σ X0)
       grind)
    | exact resolve eq4763 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4784 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (τ X0) = X1 ∨ (σ y) = X0 ∨ (k X0 (σ y)) = (k (σ y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq306 X0 X1
       have i₂ := eq4763 X0
       grind)
    | exact superpose eq4763 eq306
    | (have j1 := eq4763 X0
       grind)
    | exact resolve eq306 eq4763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306 eq4763
  have eq4836 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k y X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq4766 X0
       have i₂ := eq15 y X0
       grind)
    | exact superpose eq15 eq4766
    | (have j0 := eq4766 X0
       grind)
    | exact resolve eq4766 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4766
  have eq4845 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (σ (k X0 y)) = (σ (k y X0)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq4836 X0
       have i₂ := eq15 X0 y
       grind)
    | exact superpose eq15 eq4836
    | (have j0 := eq4836 X0
       grind)
    | exact resolve eq4836 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4836
  have eq4868 : ∀ X0 : G, (τ (σ X0)) = (k X0 X0) ∨ (σ (k X0 y)) = (σ (k y X0)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq4845 X0
       grind)
    | exact superpose eq4845 eq10
    | (have j1 := eq4845 X0
       grind)
    | exact resolve eq10 eq4845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4845
  have eq4905 : ∀ X0 : G, (σ (k X0 y)) = (σ (k y X0)) ∨ (k X0 X0) = X0 ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq4868 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4868
    | (have j0 := eq4868 X0
       grind)
    | exact resolve eq4868 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4868
  have eq4948 : ∀ X0 : G, (k y X0) = (τ (σ (k X0 y))) ∨ (k X0 X0) = X0 ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq10 (k y X0)
       have i₂ := eq4905 X0
       grind)
    | (have i₁ := eq10 (k X0 y)
       have i₂ := eq4905 X0
       grind)
    | exact superpose eq4905 eq10
    | (have j1 := eq4905 X0
       grind)
    | exact resolve eq10 eq4905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4905
  have eq4988 : ∀ X0 : G, (σ X0) = (σ y) ∨ (k X0 X0) = X0 ∨ (k X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq4948 X0
       have i₂ := eq10 (k X0 y)
       grind)
    | exact superpose eq10 eq4948
    | (have j0 := eq4948 X0
       grind)
    | exact resolve eq4948 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4948
  have eq5105 : ∀ X0 : G, (τ (σ X0)) = y ∨ (k X0 X0) = X0 ∨ (k X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq10 y
       have i₂ := eq4988 X0
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq4988 X0
       grind)
    | exact superpose eq4988 eq10
    | (have j1 := eq4988 X0
       grind)
    | exact resolve eq10 eq4988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4988
  have eq5144 : ∀ X0 : G, (k X0 X0) = X0 ∨ y = X0 ∨ (k X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq5105 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5105
    | (have j0 := eq5105 X0
       grind)
    | exact resolve eq5105 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5105
  have eq5190 : ∀ X0 : G, (k y (τ X0)) = (k (τ X0) y) ∨ (τ X0) = y ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5144 (τ X0)
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq5144
    | (have j0 := eq5144 (τ X0)
       grind)
    | exact resolve eq5144 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5204 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 ∨ y = X0 ∨ (k X0 y) = (k y X0) := by
    intro X0 X1
    first
    | (have i₁ := eq101 X0 X0
       have i₂ := eq5144 X0
       grind)
    | exact superpose eq5144 eq101
    | (have j1 := eq5144 X0
       grind)
    | exact resolve eq101 eq5144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5206 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ y = X0 ∨ (k X0 y) = (k y X0) := by
    intro X0 X1
    first
    | (have i₁ := eq305 X0 X1
       have i₂ := eq5144 X0
       grind)
    | exact superpose eq5144 eq305
    | (have j1 := eq5144 X0
       grind)
    | exact resolve eq305 eq5144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5144
  have eq5588 : ∀ X0 : G, (k X0 (σ y)) = (σ (k y (τ X0))) ∨ (τ X0) = y ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq21 X0 y
       have i₂ := eq5190 X0
       grind)
    | exact superpose eq5190 eq21
    | (have j1 := eq5190 X0
       grind)
    | exact resolve eq21 eq5190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq5190
  have eq5615 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (τ X0) = y ∨ (k X0 (σ y)) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq5588 X0
       have i₂ := eq22 X0 y
       grind)
    | exact superpose eq22 eq5588
    | (have j0 := eq5588 X0
       grind)
    | exact resolve eq5588 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5588
  have eq6203 : ∀ X0 : G, (σ (τ X0)) = (k X0 X0) ∨ (τ X0) = y ∨ (k X0 (σ y)) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq5615 X0
       grind)
    | exact superpose eq5615 eq11
    | (have j1 := eq5615 X0
       grind)
    | exact resolve eq11 eq5615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5615
  have eq6314 : ∀ X0 : G, (τ X0) = y ∨ (k X0 X0) = X0 ∨ (k X0 (σ y)) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq6203 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6203
    | (have j0 := eq6203 X0
       grind)
    | exact resolve eq6203 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6203
  have eq6435 : ∀ X0 : G, y = X0 ∨ (σ X0) = (k (σ X0) (σ X0)) ∨ (k (σ X0) (σ y)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq6314 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6314
    | (have j0 := eq6314 (σ X0)
       grind)
    | exact resolve eq6314 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6314
  have eq6575 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ y = X0 ∨ (k (σ X0) (σ y)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq6435 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq6435
    | (have j0 := eq6435 X0
       grind)
    | exact resolve eq6435 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6435
  have eq6580 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k y X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq6575 X0
       have i₂ := eq15 y X0
       grind)
    | exact superpose eq15 eq6575
    | (have j0 := eq6575 X0
       grind)
    | exact resolve eq6575 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6575
  have eq6581 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (σ (k X0 y)) = (σ (k y X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq6580 X0
       have i₂ := eq15 X0 y
       grind)
    | exact superpose eq15 eq6580
    | (have j0 := eq6580 X0
       grind)
    | exact resolve eq6580 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6580
  have eq6594 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (σ (k X0 y)) = (σ (k y X0)) ∨ y = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq305 X0 X1
       have i₂ := eq6581 X0
       grind)
    | exact superpose eq6581 eq305
    | (have j1 := eq6581 X0
       grind)
    | exact resolve eq305 eq6581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6581
  have eq17400 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (k x y) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5206 x (σ y)
       grind)
    | exact superpose eq5206 eq16
    | (have j1 := eq5206 x (σ y)
       grind)
    | (have r₁ := eq16
       have r₂ := eq5206 (M.op x y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq16 eq5206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5206
  have eq17456 : x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k x y) = (k y x) := by
    first
    | (have i₁ := eq17400
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq17400
    | exact resolve eq17400 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17400
  have eq30769 : (σ (M.op y y)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k x y) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17456
       grind)
    | exact superpose eq17456 eq16
    | exact resolve eq16 eq17456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17456
  have eq30770 : (k (σ y) (σ y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k x y) = (k y x) := by grind
  clear eq30769
  have eq30771 : (k (σ y) (σ y)) ≠ (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k x y) = (k y x) := by grind
  clear eq30770
  have eq30772 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (k x y) = (k y x) := by
    first
    | (have r₁ := eq30771
       have r₂ := eq15 y y
       grind)
    | exact resolve eq30771 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30771
  have eq30773 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (k x y) = (k y x) ∨ x = y ∨ x = y ∨ (k x y) = (k y x) := by
    first
    | (have i₁ := eq30772
       have i₂ := eq5204 x y
       grind)
    | exact superpose eq5204 eq30772
    | (have j1 := eq5204 x y
       grind)
    | (have r₁ := eq30772
       have r₂ := eq5204 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq30772
       have r₂ := eq5204 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq30772 eq5204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5204
  have eq30775 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (k x y) = (k y x) ∨ x = y := by grind
  clear eq30773
  have eq30776 : (σ x) = (σ y) ∨ (k x y) = (k y x) ∨ x = y := by grind
  clear eq30775
  have eq30780 : (σ (k y y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (k x y) = (k y x) := by
    first
    | exact superpose eq30776 eq30772
    | exact resolve eq30772 eq30776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30772 eq30776
  have eq30781 : (σ (k y y)) ≠ (σ (k y y)) ∨ (σ x) = (σ y) ∨ (k x y) = (k y x) := by grind
  clear eq30780
  have eq30782 : (k x y) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq30781
  have eq30800 : (M.op (σ x) (σ y)) = (M.op (σ (k x x)) (σ (k y x))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2597 x
       have i₂ := eq30782
       grind)
    | exact superpose eq30782 eq2597
    | (have j0 := eq2597 x
       grind)
    | exact resolve eq2597 eq30782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2597 eq30782
  have eq30812 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (k x x)) (σ (k y x))) := by grind
  clear eq30800
  have eq30815 : x = (τ (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (k x x)) (σ (k y x))) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq30812
       grind)
    | exact superpose eq30812 eq10
    | exact resolve eq10 eq30812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30812
  have eq30853 : x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ (k x x)) (σ (k y x))) := by
    first
    | (have i₁ := eq30815
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq30815
    | exact resolve eq30815 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30815
  have eq30861 : (σ (M.op y y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (k x x)) (σ (k y x))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30853
       grind)
    | exact superpose eq30853 eq16
    | exact resolve eq16 eq30853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30853
  have eq30862 : (k (σ y) (σ y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (k x x)) (σ (k y x))) := by grind
  clear eq30861
  have eq30863 : (k (σ y) (σ y)) ≠ (σ (k y y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (k x x)) (σ (k y x))) := by grind
  clear eq30862
  have eq30864 : (M.op (σ x) (σ y)) = (M.op (σ (k x x)) (σ (k y x))) := by
    first
    | (have r₁ := eq30863
       have r₂ := eq15 y y
       grind)
    | exact resolve eq30863 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30863
  have eq30930 : (M.op (σ x) (σ y)) = (k (σ (k y x)) (σ (k x x))) ∨ (σ (k x x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq305 x (σ (k y x))
       have i₂ := eq30864
       grind)
    | exact superpose eq30864 eq305
    | (have j0 := eq305 x (σ (k y x))
       grind)
    | exact resolve eq305 eq30864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq30932 : (M.op (σ x) (σ y)) = (σ (k (k y x) (k x x))) ∨ (σ (k x x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq30930
       have i₂ := eq15 (k y x) (k x x)
       grind)
    | exact superpose eq15 eq30930
    | exact resolve eq30930 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30930
  have eq36656 : ∀ X0 : G, (k y y) = (τ (σ y)) ∨ (σ X0) = y ∨ (M.op (σ X0) y) = (M.op (σ (k X0 X0)) (k (σ X0) y)) := by
    intro X0
    first
    | (have i₁ := eq10 (k y y)
       have i₂ := eq2453 X0
       grind)
    | exact superpose eq2453 eq10
    | (have j1 := eq2453 X0
       grind)
    | exact resolve eq10 eq2453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2453
  have eq36667 : ∀ X0 : G, (M.op (σ X0) y) = (M.op (σ (k X0 X0)) (k (σ X0) y)) ∨ (σ X0) = y ∨ y = (k y y) := by
    intro X0
    first
    | (have i₁ := eq36656 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq36656
    | (have j0 := eq36656 X0
       grind)
    | exact resolve eq36656 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36656
  have eq36671 : ∀ X0 : G, (M.op (σ (τ X0)) y) = (M.op (σ (τ (k X0 X0))) (k (σ (τ X0)) y)) ∨ (σ (τ X0)) = y ∨ y = (k y y) := by
    intro X0
    first
    | (have i₁ := eq36667 (τ X0)
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq36667
    | (have j0 := eq36667 (τ X0)
       grind)
    | exact resolve eq36667 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq36667
  have eq36683 : ∀ X0 : G, (M.op X0 y) = (M.op (σ (τ (k X0 X0))) (k X0 y)) ∨ (σ (τ X0)) = y ∨ y = (k y y) := by
    intro X0
    first
    | (have i₁ := eq36671 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq36671
    | (have j0 := eq36671 X0
       grind)
    | exact resolve eq36671 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36671
  have eq36684 : ∀ X0 : G, (M.op X0 y) = (M.op (k X0 X0) (k X0 y)) ∨ (σ (τ X0)) = y ∨ y = (k y y) := by
    intro X0
    first
    | (have i₁ := eq36683 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq36683
    | (have j0 := eq36683 X0
       grind)
    | exact resolve eq36683 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36683
  have eq36685 : ∀ X0 : G, (M.op X0 y) = (M.op (k X0 X0) (k X0 y)) ∨ y = X0 ∨ y = (k y y) := by
    intro X0
    first
    | (have i₁ := eq36684 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq36684
    | (have j0 := eq36684 X0
       grind)
    | exact resolve eq36684 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36684
  have eq41014 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq6594 x (σ y)
       grind)
    | exact superpose eq6594 eq16
    | (have j1 := eq6594 x (σ y)
       grind)
    | (have r₁ := eq16
       have r₂ := eq6594 (M.op x y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq16 eq6594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6594
  have eq41019 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (k y x)) ∨ x = y := by
    first
    | (have i₁ := eq41014
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq41014
    | exact resolve eq41014 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41014
  have eq48123 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 ∨ (σ X0) = (σ y) ∨ (k (σ X0) (σ y)) = (k (σ y) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4784 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4784
    | (have j0 := eq4784 (σ X0) X1
       grind)
    | exact resolve eq4784 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4784
  have eq48125 : ∀ X0 X1 : G, (k (σ X0) (σ y)) = (σ (k y X0)) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 ∨ (σ X0) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq48123 X0 X1
       have i₂ := eq15 y X0
       grind)
    | exact superpose eq15 eq48123
    | (have j0 := eq48123 X0 X1
       grind)
    | exact resolve eq48123 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48123
  have eq48126 : ∀ X0 X1 : G, (σ (k X0 y)) = (σ (k y X0)) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 ∨ (σ X0) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq48125 X0 X1
       have i₂ := eq15 X0 y
       grind)
    | exact superpose eq15 eq48125
    | (have j0 := eq48125 X0 X1
       grind)
    | exact resolve eq48125 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48125
  have eq48128 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (k y x)) ∨ x = y := by
    first
    | exact superpose eq48126 eq41019
    | (have j1 := eq48126 x y
       grind)
    | (have r₁ := eq41019
       have r₂ := eq48126 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq41019
       have r₂ := eq48126 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq41019 eq48126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41019 eq48126
  have eq48129 : x = y ∨ (σ (k x y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by grind
  clear eq48128
  have eq48133 : (σ (M.op y y)) ≠ (M.op (σ y) (σ y)) ∨ (σ (k x y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq48129
       grind)
    | exact superpose eq48129 eq16
    | exact resolve eq16 eq48129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48129
  have eq48138 : (k (σ y) (σ y)) ≠ (σ (M.op y y)) ∨ (σ (k x y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by grind
  clear eq48133
  have eq48141 : (k (σ y) (σ y)) ≠ (σ (k y y)) ∨ (σ (k x y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by grind
  clear eq48138
  have eq48143 : (σ x) = (σ y) ∨ (σ (k x y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq48141
       have r₂ := eq15 y y
       grind)
    | exact resolve eq48141 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48141
  have eq48177 : x = (τ (σ y)) ∨ (σ (k x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq48143
       grind)
    | exact superpose eq48143 eq10
    | exact resolve eq10 eq48143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48143
  have eq48268 : x = y ∨ (σ (k x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq48177
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq48177
    | exact resolve eq48177 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48177
  have eq48324 : (σ (M.op y y)) ≠ (M.op (σ y) (σ y)) ∨ (σ (k x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq48268
       grind)
    | exact superpose eq48268 eq16
    | exact resolve eq16 eq48268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48268
  have eq48331 : (k (σ y) (σ y)) ≠ (σ (M.op y y)) ∨ (σ (k x y)) = (σ (k y x)) := by grind
  clear eq48324
  have eq48335 : (k (σ y) (σ y)) ≠ (σ (k y y)) ∨ (σ (k x y)) = (σ (k y x)) := by grind
  clear eq48331
  have eq48338 : (σ (k x y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq48335
       have r₂ := eq15 y y
       grind)
    | exact resolve eq48335 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48335
  have eq48365 : (k x y) = (τ (σ (k y x))) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq48338
       grind)
    | exact superpose eq48338 eq10
    | exact resolve eq10 eq48338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48338
  have eq48487 : (k x y) = (k y x) := by
    first
    | (have i₁ := eq48365
       have i₂ := eq10 (k y x)
       grind)
    | exact superpose eq10 eq48365
    | exact resolve eq48365 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48365
  have eq48513 : x = y ∨ (M.op x y) = (M.op (k x x) (k y x)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq36685 x
       have i₂ := eq48487
       grind)
    | exact superpose eq48487 eq36685
    | (have j0 := eq36685 x
       grind)
    | exact resolve eq36685 eq48487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36685
  have eq48535 : (σ (M.op y y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (k x x) (k y x)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq48513
       grind)
    | exact superpose eq48513 eq16
    | exact resolve eq16 eq48513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48513
  have eq48541 : (k (σ y) (σ y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (M.op (k x x) (k y x)) ∨ y = (k y y) := by grind
  clear eq48535
  have eq48544 : (k (σ y) (σ y)) ≠ (σ (k y y)) ∨ (M.op x y) = (M.op (k x x) (k y x)) ∨ y = (k y y) := by grind
  clear eq48541
  have eq48546 : (M.op x y) = (M.op (k x x) (k y x)) ∨ y = (k y y) := by
    first
    | (have r₁ := eq48544
       have r₂ := eq15 y y
       grind)
    | exact resolve eq48544 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48544
  have eq48617 : (M.op x y) = (k (k y x) (k x x)) ∨ (k x x) = (k y x) ∨ y = (k y y) := by
    first
    | (have i₁ := eq101 (k y x) x
       have i₂ := eq48546
       grind)
    | exact superpose eq48546 eq101
    | (have j0 := eq101 (k y x) x
       grind)
    | exact resolve eq101 eq48546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48747 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (k x x)) = (σ (k y x)) ∨ (k x x) = (k y x) ∨ y = (k y y) := by
    first
    | (have i₁ := eq30932
       have i₂ := eq48617
       grind)
    | exact superpose eq48617 eq30932
    | exact resolve eq30932 eq48617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48617
  have eq48749 : (σ (k x x)) = (σ (k y x)) ∨ (k x x) = (k y x) ∨ y = (k y y) := by
    first
    | (have r₁ := eq48747
       have r₂ := eq16
       grind)
    | exact resolve eq48747 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48747
  have eq48776 : (k x x) = (τ (σ (k y x))) ∨ (k x x) = (k y x) ∨ y = (k y y) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq48749
       grind)
    | exact superpose eq48749 eq10
    | exact resolve eq10 eq48749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48749
  have eq48809 : (k x x) = (k y x) ∨ (k x x) = (k y x) ∨ y = (k y y) := by
    first
    | (have i₁ := eq48776
       have i₂ := eq10 (k y x)
       grind)
    | exact superpose eq10 eq48776
    | exact resolve eq48776 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48776
  have eq48810 : (k x x) = (k y x) ∨ y = (k y y) := by grind
  clear eq48809
  have eq48825 : (M.op x y) = (M.op (k y x) (k y x)) ∨ y = (k y y) := by
    first
    | exact superpose eq48810 eq48546
    | exact resolve eq48546 eq48810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48546
  have eq48832 : (M.op x y) = (k (k y x) (k y x)) ∨ y = (k y y) := by grind
  clear eq48825
  have eq48957 : (M.op (σ x) (σ y)) = (M.op (σ (k y x)) (σ (k y x))) ∨ y = (k y y) := by
    first
    | (have i₁ := eq30864
       have i₂ := eq48810
       grind)
    | exact superpose eq48810 eq30864
    | exact resolve eq30864 eq48810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48962 : (k y x) = (k (k y x) (k y x)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq61 x
       have i₂ := eq48810
       grind)
    | exact superpose eq48810 eq61
    | exact resolve eq61 eq48810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq48810
  have eq49583 : (M.op x y) = (k y x) ∨ y = (k y y) := by
    first
    | exact superpose eq48962 eq48832
    | exact resolve eq48832 eq48962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48832
  have eq49584 : (M.op (σ x) (σ y)) = (k (σ (k y x)) (σ (k y x))) ∨ y = (k y y) := by grind
  clear eq48957
  have eq49626 : (M.op (σ x) (σ y)) = (σ (k (k y x) (k y x))) ∨ y = (k y y) := by
    first
    | (have i₁ := eq49584
       have i₂ := eq15 (k y x) (k y x)
       grind)
    | exact superpose eq15 eq49584
    | exact resolve eq49584 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49584
  have eq49869 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (k y y) ∨ y = (k y y) := by
    first
    | (have i₁ := eq49626
       have i₂ := eq48962
       grind)
    | exact superpose eq48962 eq49626
    | exact resolve eq49626 eq48962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48962 eq49626
  have eq49889 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (k y y) := by grind
  clear eq49869
  have eq49951 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq49889
       grind)
    | exact superpose eq49889 eq16
    | exact resolve eq16 eq49889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49889
  have eq49991 : (σ (k y x)) ≠ (σ (k y x)) ∨ y = (k y y) ∨ y = (k y y) := by
    first
    | (have i₁ := eq49951
       have i₂ := eq49583
       grind)
    | exact superpose eq49583 eq49951
    | exact resolve eq49951 eq49583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49583 eq49951
  have eq50015 : (σ (k y x)) ≠ (σ (k y x)) ∨ y = (k y y) := by grind
  clear eq49991
  have eq50016 : y = (k y y) := by grind
  clear eq50015
  have eq50260 : ∀ X0 : G, (M.op X0 y) = (M.op (k X0 X0) (k X0 y)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq315 X0 y
       have i₂ := eq50016
       grind)
    | exact superpose eq50016 eq315
    | exact resolve eq315 eq50016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315 eq50016
  have eq51314 : x = y ∨ (M.op x y) = (M.op (k x x) (k y x)) := by
    first
    | (have i₁ := eq50260 x
       have i₂ := eq48487
       grind)
    | exact superpose eq48487 eq50260
    | (have j0 := eq50260 x
       grind)
    | exact resolve eq50260 eq48487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48487 eq50260
  have eq51336 : (σ (M.op y y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (k x x) (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq51314
       grind)
    | exact superpose eq51314 eq16
    | exact resolve eq16 eq51314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51314
  have eq51339 : (k (σ y) (σ y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (M.op (k x x) (k y x)) := by grind
  clear eq51336
  have eq51341 : (k (σ y) (σ y)) ≠ (σ (k y y)) ∨ (M.op x y) = (M.op (k x x) (k y x)) := by grind
  clear eq51339
  have eq51343 : (M.op x y) = (M.op (k x x) (k y x)) := by
    first
    | (have r₁ := eq51341
       have r₂ := eq15 y y
       grind)
    | exact resolve eq51341 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51341
  have eq51463 : (M.op x y) = (k (k y x) (k x x)) ∨ (k x x) = (k y x) := by
    first
    | (have i₁ := eq101 (k y x) x
       have i₂ := eq51343
       grind)
    | exact superpose eq51343 eq101
    | (have j0 := eq101 (k y x) x
       grind)
    | exact resolve eq101 eq51343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq52334 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (k x x)) = (σ (k y x)) ∨ (k x x) = (k y x) := by
    first
    | (have i₁ := eq30932
       have i₂ := eq51463
       grind)
    | exact superpose eq51463 eq30932
    | exact resolve eq30932 eq51463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30932 eq51463
  have eq52353 : (σ (k x x)) = (σ (k y x)) ∨ (k x x) = (k y x) := by
    first
    | (have r₁ := eq52334
       have r₂ := eq16
       grind)
    | exact resolve eq52334 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52334
  have eq52517 : (k x x) = (τ (σ (k y x))) ∨ (k x x) = (k y x) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq52353
       grind)
    | exact superpose eq52353 eq10
    | exact resolve eq10 eq52353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52353
  have eq52550 : (k x x) = (k y x) ∨ (k x x) = (k y x) := by
    first
    | (have i₁ := eq52517
       have i₂ := eq10 (k y x)
       grind)
    | exact superpose eq10 eq52517
    | exact resolve eq52517 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52517
  have eq52551 : (k x x) = (k y x) := by grind
  clear eq52550
  have eq52581 : (M.op (σ x) (σ y)) = (M.op (σ (k y x)) (σ (k y x))) := by
    first
    | (have i₁ := eq30864
       have i₂ := eq52551
       grind)
    | exact superpose eq52551 eq30864
    | exact resolve eq30864 eq52551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30864
  have eq52613 : (M.op x y) = (M.op (k y x) (k y x)) := by
    first
    | (have i₁ := eq51343
       have i₂ := eq52551
       grind)
    | exact superpose eq52551 eq51343
    | exact resolve eq51343 eq52551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51343 eq52551
  have eq52635 : (M.op x y) = (k (k y x) (k y x)) := by grind
  clear eq52613
  have eq52637 : (M.op (σ x) (σ y)) = (k (σ (k y x)) (σ (k y x))) := by grind
  clear eq52581
  have eq52642 : (M.op (σ x) (σ y)) = (σ (k (k y x) (k y x))) := by
    first
    | (have i₁ := eq52637
       have i₂ := eq15 (k y x) (k y x)
       grind)
    | exact superpose eq15 eq52637
    | exact resolve eq52637 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52637
  have eq52646 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq52642
       have i₂ := eq52635
       grind)
    | exact superpose eq52635 eq52642
    | exact resolve eq52642 eq52635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52635 eq52642
  have eq52649 : False := by grind
  exact eq52649

/-- `Equation3744`: `x ◇ y = (x ◇ z) ◇ (w ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_x_y_pyx_Equation3744 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3744 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3744.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
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
  have eq37 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
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
  have eq50 : y ≠ (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op x y) (M.op X1 X0)) := by
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
  have eq57 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op (σ x) (σ y)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y) X1
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X5 X3)) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 (M.op X0 X2) X3 (M.op x X1) X5
       have i₂ := eq14 X0 X1 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op X0 X1) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 y X1 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 y X1 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op (M.op X0 X1) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) X1 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X4) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X2 (M.op X3 X1) X4 (M.op X0 x)
       have i₂ := eq14 X0 X1 x X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X3 X1) ∨ (M.op X0 X2) = (k (M.op X0 X2) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op X0 X2) (M.op X3 X1)
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op X0 X2) (M.op X3 X1)
       grind)
    | (have r₁ := eq13 (M.op X0 X2) (M.op X0 X1)
       have r₂ := eq14 X0 X1 X2 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X2 X1) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq61 x X1 X2 X3 x
       have i₂ := eq14 X2 X1 x x
       grind)
    | exact superpose eq14 eq61
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq64 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X0 X2) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq58 X0 x X2 X3 x
       have i₂ := eq14 X0 X3 x x
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq80 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq81 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq87 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq80
       grind)
    | exact superpose eq80 eq16
    | exact resolve eq16 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
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
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq95
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq95
    | exact resolve eq95 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq105
    | exact resolve eq105 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq106
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq106
    | exact resolve eq106 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq108 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
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
  have eq114 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq108
  have eq134 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq217 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq56 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq56
    | (have j0 := eq56 y x
       grind)
    | exact resolve eq56 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : (M.op x (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq217 eq56
    | exact resolve eq56 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq231 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq217 eq13
    | (have j0 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq217
       grind)
    | exact resolve eq13 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq231
  have eq234 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq217 eq228
    | exact resolve eq228 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq228
  have eq236 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq232 eq134
    | exact resolve eq134 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq232
  have eq240 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq236
    | exact resolve eq236 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq245 : (M.op x y) ≠ (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq234 eq13
    | (have j0 := eq13 x (M.op x y)
       grind)
    | (have r₁ := eq13 x (M.op x y)
       have r₂ := eq234
       grind)
    | exact resolve eq13 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : x = (k x (M.op x y)) := by grind
  clear eq245
  have eq253 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq57
    | (have j0 := eq57 (σ y) (σ x)
       grind)
    | exact resolve eq57 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258 : ∀ X0 X1 X3 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (M.op (σ x) X0) (M.op X3 X1)) := by
    intro X0 X1 X3
    first
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq260 : ∀ X1 : G, (M.op (σ x) X1) = (M.op (M.op (σ x) (σ y)) X1) := by
    intro X1
    first
    | (have i₁ := eq258 x X1 x
       have i₂ := eq14 sF2 X1 x x
       grind)
    | exact superpose eq14 eq258
    | exact resolve eq258 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq266 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq253 eq57
    | exact resolve eq57 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq273 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq253 eq266
    | exact resolve eq266 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253 eq266
  have eq326 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq240 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq327 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq326
  have eq345 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op (M.op X1 X2) (M.op X0 (σ y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq60 eq14
    | exact resolve eq14 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352 : ∀ X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op X1 (σ y)) := by
    intro X1
    first
    | (have i₁ := eq345 x x x
       have i₂ := eq14 x sF3 x x
       grind)
    | exact superpose eq14 eq345
    | exact resolve eq345 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq375 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq246 eq45
    | exact resolve eq45 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq246
  have eq379 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq375
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq375
    | exact resolve eq375 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq394 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (k X0 (M.op X2 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op X2 X1)
       have i₂ := eq63 X1 X0 X2
       grind)
    | exact superpose eq63 eq13
    | (have j0 := eq13 X0 (M.op X2 X1)
       grind)
    | (have r₁ := eq13 X2 (M.op X2 X1)
       have r₂ := eq63 X1 X2 X2
       grind)
    | exact resolve eq13 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq467 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq379 eq11
    | (have j0 := eq11 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379
  have eq468 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq467
  have eq575 : ∀ X0 : G, (M.op (σ x) X0) ≠ X0 ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq260 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | exact resolve eq13 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq694 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op (M.op (σ x) (σ y)) X0) = X0 ∨ (k (M.op (σ x) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq352 eq12
    | (have j0 := eq12 (M.op (σ x) (σ y)) X0
       grind)
    | (have r₁ := eq12 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq352 (σ x)
       grind)
    | exact resolve eq12 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq718 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op (σ x) X0) = X0 ∨ (k (M.op (σ x) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq260 eq694
    | (have j0 := eq694 X0
       grind)
    | (have r₁ := eq694 (M.op (σ x) (σ y))
       have r₂ := eq260 (σ y)
       grind)
    | exact resolve eq694 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260 eq694
  have eq770 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq62 X0 X2 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq1003 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq88 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq88 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq88 X0 X1
       grind)
    | exact resolve eq13 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1012 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (M.op X2 (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 (σ X0) X2 (σ X1)
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq63
    | (have j1 := eq88 X0 X1
       grind)
    | exact resolve eq63 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq1016 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq88 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq1026 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1003 X0 X1
       have j1 := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq1003 X0 X1
       have r₂ := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq1003 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq1003 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003
  have eq1034 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1026 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq1026
    | (have j0 := eq1026 X0 X1
       grind)
    | exact resolve eq1026 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026
  have eq1239 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (k (M.op (σ (M.op x y)) X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq327 eq770
    | exact resolve eq770 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq1563 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq394 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq2679 : (M.op (σ (M.op x y)) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq468 eq60
    | exact resolve eq60 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468
  have eq2696 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq273 eq2679
    | exact resolve eq2679 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2679
  have eq3172 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2696 eq1239
    | exact resolve eq1239 eq2696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239
  have eq3203 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq575 (σ (M.op x y))
       grind)
    | (have r₁ := eq3172
       have r₂ := eq575 (σ (M.op x y))
       grind)
    | exact resolve eq3172 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575 eq3172
  have eq8343 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1012 y y X0
       have i₂ := eq81
       grind)
    | exact superpose eq81 eq1012
    | (have j0 := eq1012 y y x
       grind)
    | exact resolve eq1012 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq1012
  have eq8422 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq8343 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8343
  have eq8449 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq8422 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8422
    | (have j0 := eq8422 X0
       grind)
    | exact resolve eq8422 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8422
  have eq8521 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq8449 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8449
    | (have j0 := eq8449 X0
       grind)
    | exact resolve eq8449 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8449
  have eq13678 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq107 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq13684 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq13678
    | exact resolve eq13678 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13678
  have eq13695 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq13684
       have r₂ := eq27
       grind)
    | exact resolve eq13684 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13684
  have eq13700 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq13695
    | exact resolve eq13695 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13695
  have eq13723 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq13700 eq1563
    | exact resolve eq1563 eq13700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13700
  have eq13743 : (τ (σ y)) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq13723 eq87
    | exact resolve eq87 eq13723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13723
  have eq13769 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq13743
    | exact resolve eq13743 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13743
  have eq13772 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq13769
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13769
       have r₂ := eq13 x y
       grind)
    | (have r₁ := eq13769
       have r₂ := eq13 y x
       grind)
    | exact resolve eq13769 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13769
  have eq13884 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1016 x y
       have i₂ := eq13772
       grind)
    | exact superpose eq13772 eq1016
    | (have j0 := eq1016 x y
       grind)
    | exact resolve eq1016 eq13772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016
  have eq13885 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1034 y x
       have i₂ := eq13772
       grind)
    | exact superpose eq13772 eq1034
    | (have j0 := eq1034 y x
       grind)
    | exact resolve eq1034 eq13772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034 eq13772
  have eq13888 : (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq13885
  have eq13889 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq13884
  have eq13893 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13888
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq13888
    | exact resolve eq13888 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq13888
  have eq13894 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13889
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13889
    | exact resolve eq13889 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13889
  have eq13908 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13893
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13893
    | exact resolve eq13893 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13893
  have eq13909 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13894
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13894
    | exact resolve eq13894 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13894
  have eq13912 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq13908
       have r₂ := eq51
       grind)
    | exact resolve eq13908 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq13908
  have eq13913 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq13909
    | exact resolve eq13909 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13909
  have eq13914 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq13913
  have eq13917 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13912
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13912
    | exact resolve eq13912 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13912
  have eq13918 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13914
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13914
    | exact resolve eq13914 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq13914
  have eq13920 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13917
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13917
    | exact resolve eq13917 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13917
  have eq13921 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13918
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13918
    | exact resolve eq13918 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13918
  have eq14119 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13921 eq60
    | exact resolve eq60 eq13921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13921
  have eq14144 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq273 eq14119
    | exact resolve eq14119 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273 eq14119
  have eq15141 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13920 eq55
    | exact resolve eq55 eq13920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq13920
  have eq15168 : x = (k x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq15141
    | exact resolve eq15141 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq15141
  have eq15173 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (k x y) := by
    first
    | (have r₁ := eq15168
       have r₂ := eq50
       grind)
    | exact resolve eq15168 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq15168
  have eq15195 : (σ y) = (k (σ y) (σ x)) ∨ x = (k x y) := by
    first
    | exact superpose eq15173 eq1563
    | exact resolve eq1563 eq15173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15173
  have eq15329 : (τ (σ y)) = (k y x) ∨ x = (k x y) := by
    first
    | exact superpose eq15195 eq87
    | exact resolve eq87 eq15195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq15195
  have eq15354 : y = (k y x) ∨ x = (k x y) := by
    first
    | exact superpose eq29 eq15329
    | exact resolve eq15329 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq15329
  have eq15413 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq15354
       grind)
    | exact superpose eq15354 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq15354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15354
  have eq15421 : y = (M.op x y) ∨ x = (M.op y x) ∨ x = (k x y) := by grind
  clear eq15413
  have eq15427 : x = (k x y) ∨ x = (M.op y x) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq15421
       have r₂ := eq13 x y
       grind)
    | (have r₁ := eq15421
       have r₂ := eq13 y x
       grind)
    | exact resolve eq15421 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15421
  have eq15479 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq15427
       grind)
    | exact superpose eq15427 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq15427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15427
  have eq15487 : x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq15479
  have eq15493 : x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15487
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15487
    | exact resolve eq15487 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq15487
  have eq15527 : (M.op x (M.op x y)) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq59 y x
       have i₂ := eq15493
       grind)
    | exact superpose eq15493 eq59
    | exact resolve eq59 eq15493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq15493
  have eq15552 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq234 eq15527
    | exact resolve eq15527 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234 eq15527
  have eq15601 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq114
       have i₂ := eq15552
       grind)
    | exact superpose eq15552 eq114
    | exact resolve eq114 eq15552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq15552
  have eq15642 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq15601
  have eq15648 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq15642
    | exact resolve eq15642 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15642
  have eq24316 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2696 eq718
    | (have j0 := eq718 (σ (M.op x y))
       grind)
    | (have r₁ := eq718 (σ (M.op x y))
       have r₂ := eq2696
       grind)
    | exact resolve eq718 eq2696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718 eq2696
  have eq24334 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by grind
  clear eq24316
  have eq24335 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by grind
  clear eq24334
  have eq24340 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq3203 eq24335
    | exact resolve eq24335 eq3203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3203 eq24335
  have eq24345 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq24340
       have r₂ := eq27
       grind)
    | exact resolve eq24340 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24340
  have eq24362 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq24345 eq60
    | exact resolve eq60 eq24345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq24365 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq24345 eq64
    | exact resolve eq64 eq24345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq24345
  have eq24390 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq352 eq24362
    | exact resolve eq24362 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352 eq24362
  have eq24394 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq26 eq24390
    | exact resolve eq24390 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24390
  have eq24818 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq24365 eq8521
    | exact resolve eq8521 eq24365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8521 eq24365
  have eq24844 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq24818
    | exact resolve eq24818 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq24818
  have eq26551 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15648 eq24844
    | exact resolve eq24844 eq15648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24844
  have eq26608 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq327 eq26551
    | exact resolve eq26551 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26551
  have eq26612 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq26608
       have r₂ := eq27
       grind)
    | exact resolve eq26608 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26608
  have eq26635 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26612 eq14144
    | exact resolve eq14144 eq26612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14144
  have eq26666 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26612 eq1563
    | exact resolve eq1563 eq26612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1563 eq26612
  have eq26674 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq26635
  have eq26696 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26674 eq27
    | exact resolve eq27 eq26674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26674
  have eq26789 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26666 eq15648
    | exact resolve eq15648 eq26666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15648 eq26666
  have eq26807 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq26789
  have eq26816 : y = (M.op x y) := by
    first
    | (have r₁ := eq26807
       have r₂ := eq26696
       grind)
    | exact resolve eq26807 eq26696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26696 eq26807
  have eq26831 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq26816 eq20
    | exact resolve eq20 eq26816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq26816
  have eq26957 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq26831
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq26831
    | exact resolve eq26831 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq26831
  have eq27098 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq26957 eq24394
    | exact resolve eq24394 eq26957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24394 eq26957
  have eq27109 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq327 eq27098
    | exact resolve eq27098 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327 eq27098
  have eq27194 : False := by grind
  exact eq27194

/-- `Equation3744`: `x ◇ y = (x ◇ z) ◇ (w ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else Y`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_y_Equation3744 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) Law3744 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3744.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq62 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X5 X3)) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq9 (M.op X0 X2) X3 (M.op x X1) X5
       have i₂ := eq9 X0 X1 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X4) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X2 (M.op X3 X1) X4 (M.op X0 x)
       have i₂ := eq9 X0 X1 x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X2 X1) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq63 x X1 X2 X3 x
       have i₂ := eq9 X2 X1 x x
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq65 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X0 X2) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq62 X0 x X2 X3 x
       have i₂ := eq9 X0 X3 x x
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq90 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X2 (M.op X0 X1)) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X0 X1)
       have i₂ := eq9 X0 X1 X1 X0
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X2 (M.op X0 X1)
       grind)
    | (have r₁ := eq12 X0 (M.op x X1)
       have r₂ := eq9 x X1 X1 x
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq90 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq96 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq93 X0 X1 X2
       have i₂ := eq64 X1 X2 X0
       grind)
    | exact superpose eq64 eq93
    | exact resolve eq93 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq93
  have eq103 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X2 X1))) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (M.op X2 X1)
       have i₂ := eq96 X2 X1 (τ X0)
       grind)
    | exact superpose eq96 eq18
    | exact resolve eq18 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq109 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq129 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) = (σ (M.op (τ (σ (M.op X0 X1))) X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    grind
  have eq130 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) = (σ (M.op (M.op X0 X1) X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq129 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq129
    | (have j0 := eq129 X0 X1
       grind)
    | exact resolve eq129 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq138 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq130 X0 X1
       have i₂ := eq65 X0 X1 X1
       grind)
    | exact superpose eq65 eq130
    | (have j0 := eq130 X0 X1
       grind)
    | exact resolve eq130 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq139 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq138 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq203 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (k X2 (σ (M.op X0 X1))) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (σ (M.op X0 X1))
       have i₂ := eq139 X0 X1
       grind)
    | exact superpose eq139 eq12
    | (have j0 := eq12 X2 (σ (M.op X0 X1))
       grind)
    | (have r₁ := eq12 X0 (σ (M.op X0 X1))
       have r₂ := eq139 X0 X1
       grind)
    | exact resolve eq12 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq204 : ∀ X0 X1 X2 : G, (k X2 (σ (M.op X0 X1))) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq203 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq205 : ∀ X0 X1 X2 : G, (σ (M.op (τ X2) X1)) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq204 X0 X1 X2
       have i₂ := eq103 X2 X1 X0
       grind)
    | exact superpose eq103 eq204
    | exact resolve eq204 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq233 : ∀ X0 X1 X2 X3 : G, (σ (M.op (τ (M.op X0 X1)) X2)) = (M.op X0 (σ (M.op X3 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq65 X0 X1 (σ (M.op X3 X2))
       have i₂ := eq205 X3 X2 (M.op X0 X1)
       grind)
    | exact superpose eq205 eq65
    | exact resolve eq65 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : ∀ X0 X1 X2 : G, (σ (M.op (τ X0) X2)) = (σ (M.op (τ (M.op X0 X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq233 X0 X1 X2 x
       have i₂ := eq205 x X2 X0
       grind)
    | exact superpose eq205 eq233
    | exact resolve eq233 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205 eq233
  have eq1055 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq109 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq109
    | exact resolve eq109 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq1109 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1055 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq1055
    | (have j0 := eq1055 X0
       grind)
    | exact resolve eq1055 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1055
  have eq1120 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1109 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1109
    | (have j0 := eq1109 X0
       grind)
    | exact resolve eq1109 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109
  have eq1127 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1120 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq1120 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq1120 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120
  have eq1139 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1127 (σ X0)
       grind)
    | exact superpose eq1127 eq15
    | exact resolve eq15 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1146 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1139 X0
       have i₂ := eq1127 X0
       grind)
    | exact superpose eq1127 eq1139
    | exact resolve eq1139 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127 eq1139
  have eq1187 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 X0))) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq96 (σ X0) (σ X0) X1
       have i₂ := eq1146 X0
       grind)
    | exact superpose eq1146 eq96
    | exact resolve eq96 eq1146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq1193 : ∀ X0 X1 : G, (σ (M.op (τ (σ X0)) X1)) = (σ (M.op (τ (σ (M.op X0 X0))) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq234 (σ X0) (σ X0) X1
       have i₂ := eq1146 X0
       grind)
    | exact superpose eq1146 eq234
    | exact resolve eq234 eq1146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234 eq1146
  have eq1204 : ∀ X0 X1 : G, (σ (M.op (τ (σ X0)) X1)) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1193 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1193
    | exact resolve eq1193 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193
  have eq1208 : ∀ X0 X1 : G, (σ (M.op (τ X1) X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1187 X0 X1
       have i₂ := eq103 X1 X0 X0
       grind)
    | exact superpose eq103 eq1187
    | exact resolve eq1187 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq1187
  have eq1231 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1204 X0 X1
       have i₂ := eq65 X0 X0 X1
       grind)
    | exact superpose eq65 eq1204
    | exact resolve eq1204 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq1204
  have eq1246 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1231 X0 X1
       have i₂ := eq1208 X1 (σ X0)
       grind)
    | exact superpose eq1208 eq1231
    | exact resolve eq1231 eq1208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208 eq1231
  have eq1686 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1246 x y
       grind)
    | exact superpose eq1246 eq16
    | (have r₁ := eq16
       have r₂ := eq1246 x y
       grind)
    | exact resolve eq16 eq1246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1246
  have eq1719 : False := by grind
  exact eq1719

/-- `Equation4512`: `x ◇ (y ◇ z) = (x ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_x_pyx_Equation4512 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4512 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4512.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X1) X2) := by
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
  have eq37 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
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
  have eq72 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq152 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq72 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq72
    | exact resolve eq72 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (M.op x (M.op y X0)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (k X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 (M.op X0 X1)
       have i₂ := eq174 (M.op X0 X1)
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : (M.op (M.op x y) y) = (M.op x (k y y)) := by
    first
    | (have i₁ := eq175 y
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq175
    | exact resolve eq175 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq320 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq404 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq320 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq320
    | exact resolve eq320 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq558 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq559 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq558 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq558
    | (have j0 := eq558 X0
       grind)
    | exact resolve eq558 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq562 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq559 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq559
    | (have j0 := eq559 X0
       grind)
    | exact resolve eq559 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq690 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op (k X0 X1) X2) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0 X2
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq691 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X2)) = (M.op X1 (M.op X2 X0)) ∨ (M.op X1 X2) = (M.op X0 X0) ∨ (M.op X1 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0
       have i₂ := eq11 X0 (M.op X1 X2)
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 (M.op X1 X2)
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : (M.op x y) = (k y x) ∨ x = (M.op y y) ∨ x = y := by
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
  have eq697 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
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
  have eq705 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq697
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq697
    | exact resolve eq697 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq709 : (M.op x y) = (k y x) ∨ x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq693
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq693
    | exact resolve eq693 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq711 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X2)) = (M.op X1 (M.op X2 X0)) ∨ (M.op X1 X2) = (k X0 X0) ∨ (M.op X1 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq691 X0 X1 X2
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq691
    | (have j0 := eq691 X0 X1 X2
       grind)
    | exact resolve eq691 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq712 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op (k X0 X1) X2) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq690 X0 X1 X2
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq690
    | (have j0 := eq690 X0 X1 X2
       grind)
    | exact resolve eq690 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq731 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq709
       grind)
    | exact superpose eq709 eq39
    | exact resolve eq39 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq732 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq731
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq731
    | exact resolve eq731 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq734 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k y y) ∨ x = y := by
    first
    | exact superpose eq20 eq732
    | exact resolve eq732 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq737 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y := by
    first
    | exact superpose eq734 eq705
    | exact resolve eq705 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705 eq734
  have eq744 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y := by
    first
    | (have r₁ := eq737
       have r₂ := eq27
       grind)
    | exact resolve eq737 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737
  have eq750 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y := by
    first
    | exact superpose eq744 eq115
    | exact resolve eq115 eq744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq744
  have eq759 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y := by
    first
    | exact superpose eq29 eq750
    | exact resolve eq750 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq760 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq759
  have eq767 : (M.op (M.op x y) y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq183
       have i₂ := eq760
       grind)
    | exact superpose eq760 eq183
    | exact resolve eq183 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq769 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq760
       grind)
    | exact superpose eq760 eq40
    | exact resolve eq40 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq772 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq181 y X0
       have i₂ := eq760
       grind)
    | exact superpose eq760 eq181
    | exact resolve eq181 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq774 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq769
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq769
    | exact resolve eq769 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq776 : (k x x) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq767
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq767
    | exact resolve eq767 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq777 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq774
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq774
    | exact resolve eq774 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq795 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq777 eq181
    | exact resolve eq181 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq832 : ∀ X0 : G, (M.op x (M.op y X0)) = (M.op y (M.op x X0)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq772 (M.op y X0)
       have i₂ := eq772 X0
       grind)
    | exact superpose eq772 eq772
    | exact resolve eq772 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq833 : (M.op x y) = (M.op y (k y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq772 y
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq772
    | exact resolve eq772 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq839 : ∀ X0 : G, (M.op x (M.op y X0)) = (M.op y (M.op x X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq832 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832
  have eq844 : (M.op x y) = (M.op y (k y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq833
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq833
    | exact resolve eq833 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833
  have eq845 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op y (M.op x X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq839 X0
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq839
    | exact resolve eq839 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839
  have eq849 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq760 eq844
    | exact resolve eq844 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq851 : (M.op x x) = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq772 x
       have i₂ := eq849
       grind)
    | exact superpose eq849 eq772
    | exact resolve eq772 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq852 : (M.op (M.op x y) x) = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq175 x
       have i₂ := eq849
       grind)
    | exact superpose eq849 eq175
    | exact resolve eq175 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq853 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq849
       grind)
    | exact superpose eq849 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq855 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq853
  have eq856 : (M.op x x) = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq851
  have eq858 : (M.op x y) = (k x y) ∨ y = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq855
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq855
    | exact resolve eq855 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq859 : (k x x) = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq856
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq856
    | exact resolve eq856 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq868 : (M.op x (M.op x y)) = (M.op y (k x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq859 eq772
    | exact resolve eq772 eq859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq869 : (M.op (M.op x y) (M.op x y)) = (M.op x (k x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq859 eq175
    | exact resolve eq175 eq859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq872 : (M.op x (M.op x y)) = (M.op y (k x x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq868
  have eq875 : (k (M.op x y) (M.op x y)) = (M.op x (k x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq869
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq869
    | exact resolve eq869 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq876 : (M.op (M.op x y) x) = (M.op y (k x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq852 eq872
    | exact resolve eq872 eq852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852 eq872
  have eq879 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op (σ y) (M.op (σ x) X0)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq795 eq795
    | exact resolve eq795 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq880 : (M.op (σ x) (σ y)) = (M.op (σ y) (k (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq795 sF3
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq795
    | exact resolve eq795 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq881 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) (k X0 (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op X0 X0) = (σ y) ∨ (σ y) = X0 := by
    intro X0
    first
    | (have i₁ := eq795 X0
       have i₂ := eq11 X0 sF3
       grind)
    | exact superpose eq11 eq795
    | (have j1 := eq11 X0 (σ y)
       grind)
    | exact resolve eq795 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq886 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op (σ y) (M.op (σ x) X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq879 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879
  have eq890 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) (k X0 (σ y))) ∨ (σ y) = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = X0 := by
    intro X0
    first
    | (have i₁ := eq881 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq881
    | (have j0 := eq881 X0
       grind)
    | exact resolve eq881 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881
  have eq891 : (M.op (σ x) (σ y)) = (M.op (σ y) (k (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq880
    | exact resolve eq880 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880
  have eq892 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ y) (M.op (σ x) X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq176 eq886
    | exact resolve eq886 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886
  have eq896 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq777 eq891
    | exact resolve eq891 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891
  have eq898 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq896 eq795
    | exact resolve eq795 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq899 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq896 eq176
    | exact resolve eq176 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq900 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq896 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq902 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq900
  have eq903 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq898
  have eq905 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq902
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq902
    | exact resolve eq902 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902
  have eq906 : (k (σ x) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq903
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq903
    | exact resolve eq903 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq915 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq906 eq795
    | exact resolve eq795 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq916 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq906 eq176
    | exact resolve eq176 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq919 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq915
  have eq922 : (M.op (σ x) (k (σ x) (σ x))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq916
       have i₂ := eq174 sF4
       grind)
    | exact superpose eq174 eq916
    | exact resolve eq916 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq929 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op y (k X0 x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op X0 X0) = x ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq845 X0
       have i₂ := eq11 X0 x
       grind)
    | exact superpose eq11 eq845
    | (have j1 := eq11 X0 x
       grind)
    | exact resolve eq845 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq941 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op y (k X0 x)) ∨ x = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq929 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq929
    | (have j0 := eq929 X0
       grind)
    | exact resolve eq929 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929
  have eq1012 : (M.op (M.op (σ x) (σ y)) (k (σ x) (σ x))) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq919 eq176
    | exact resolve eq176 eq919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq1023 : (M.op (M.op (σ x) (σ y)) (k (σ x) (σ x))) = (M.op (σ y) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq922 eq892
    | exact resolve eq892 eq922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1026 : (M.op (M.op (σ x) (σ y)) (k (σ x) (σ x))) = (M.op (σ y) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1023
  have eq1029 : (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (σ y) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1012 eq1026
    | exact resolve eq1026 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012 eq1026
  have eq1044 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq858
       grind)
    | exact superpose eq858 eq40
    | exact resolve eq40 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858
  have eq1045 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1044
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1044
    | exact resolve eq1044 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044
  have eq1047 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq1045
    | exact resolve eq1045 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045
  have eq1055 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1047 eq905
    | exact resolve eq905 eq1047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905 eq1047
  have eq1059 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k x x) := by grind
  clear eq1055
  have eq1064 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k x x) := by
    first
    | (have r₁ := eq1059
       have r₂ := eq27
       grind)
    | exact resolve eq1059 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059
  have eq1071 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k x x) := by
    first
    | exact superpose eq1064 eq97
    | exact resolve eq97 eq1064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq1064
  have eq1082 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k x x) := by
    first
    | exact superpose eq31 eq1071
    | exact resolve eq1071 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071
  have eq1083 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1082
  have eq1274 : (M.op y y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq876
       have i₂ := eq1083
       grind)
    | exact superpose eq1083 eq876
    | exact resolve eq876 eq1083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1275 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq875
       have i₂ := eq1083
       grind)
    | exact superpose eq1083 eq875
    | exact resolve eq875 eq1083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875
  have eq1278 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq1083
       grind)
    | exact superpose eq1083 eq39
    | exact resolve eq39 eq1083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1280 : x = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq562 x
       have i₂ := eq1083
       grind)
    | exact superpose eq1083 eq562
    | exact resolve eq562 eq1083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq1281 : ∀ X0 : G, (M.op y X0) = (M.op x (M.op x X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq181 x X0
       have i₂ := eq1083
       grind)
    | exact superpose eq1083 eq181
    | exact resolve eq181 eq1083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1282 : x = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1280
  have eq1283 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1275
  have eq1284 : (M.op y y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1274
  have eq1285 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1278
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1278
    | exact resolve eq1278 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1278
  have eq1287 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1283
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1283
    | exact resolve eq1283 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1283
  have eq1288 : (k y y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1284
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq1284
    | exact resolve eq1284 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1284
  have eq1289 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1285
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1285
    | exact resolve eq1285 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285
  have eq1291 : x = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq760 eq1288
    | exact resolve eq1288 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288
  have eq1295 : (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1282
       grind)
    | exact superpose eq1282 eq40
    | exact resolve eq40 eq1282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1300 : (σ x) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1295
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1295
    | exact resolve eq1295 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295
  have eq1305 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1287 eq41
    | exact resolve eq41 eq1287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1307 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op (M.op x y) X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1287 eq181
    | exact resolve eq181 eq1287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1308 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq1305
    | exact resolve eq1305 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1305
  have eq1310 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1289 eq922
    | exact resolve eq922 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq1311 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1289 eq919
    | exact resolve eq919 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919
  have eq1318 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) (M.op (σ x) X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1289 eq181
    | exact resolve eq181 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1320 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1311
  have eq1321 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1310
  have eq1325 : (k (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1320
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq1320
    | exact resolve eq1320 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320
  have eq1326 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq1321
    | exact resolve eq1321 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321
  have eq1329 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq777 eq1325
    | exact resolve eq1325 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325
  have eq1362 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1308 eq181
    | exact resolve eq181 eq1308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq1370 : ∀ X0 : G, (M.op X0 (σ x)) = (k (M.op (σ x) (σ y)) (M.op X0 (σ x))) ∨ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op X0 (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1329 eq711
    | (have j0 := eq711 (M.op (σ x) (σ y)) X0 (σ x)
       grind)
    | exact resolve eq711 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1371 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1329 eq11
    | (have j0 := eq11 (M.op (σ x) (σ y)) (σ x)
       grind)
    | exact resolve eq11 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1374 : (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1371
       have i₂ := eq174 sF4
       grind)
    | exact superpose eq174 eq1371
    | exact resolve eq1371 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1371
  have eq1375 : ∀ X0 : G, (M.op X0 (σ x)) = (k (M.op (σ x) (σ y)) (M.op X0 (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op X0 (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1326 eq1370
    | (have j0 := eq1370 X0
       grind)
    | exact resolve eq1370 eq1326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1370
  have eq1376 : ∀ X0 : G, (M.op X0 (σ x)) = (k (M.op (σ x) (σ y)) (M.op X0 (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq1375 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1375
  have eq1400 : (M.op y y) = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1281 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1281
    | (have j0 := eq1281 y
       grind)
    | exact resolve eq1281 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281
  have eq1425 : (k y y) = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1400
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq1400
    | exact resolve eq1400 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1400
  have eq1437 : x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq760 eq1425
    | exact resolve eq1425 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1425
  have eq1457 : ∀ X0 : G, (M.op X0 x) = (k (M.op x y) (M.op X0 x)) ∨ (k (M.op x y) (M.op x y)) = (M.op X0 x) ∨ (M.op x y) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1437 eq711
    | (have j0 := eq711 (M.op x y) X0 x
       grind)
    | exact resolve eq711 eq1437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1437
  have eq1465 : ∀ X0 : G, (M.op X0 x) = (k (M.op x y) (M.op X0 x)) ∨ (M.op x y) = (M.op X0 x) ∨ (M.op x y) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1287 eq1457
    | (have j0 := eq1457 X0
       grind)
    | exact resolve eq1457 eq1287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1287 eq1457
  have eq1466 : ∀ X0 : G, (M.op X0 x) = (k (M.op x y) (M.op X0 x)) ∨ (M.op x y) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq1465 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465
  have eq1492 : (k x x) = (M.op (M.op x y) (k x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq776 eq1307
    | exact resolve eq1307 eq776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776 eq1307
  have eq1506 : (k x x) = (M.op (M.op x y) (k x x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1492
  have eq1514 : y = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1083 eq1506
    | exact resolve eq1506 eq1083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1506
  have eq1532 : ∀ X0 : G, (M.op y X0) = (M.op (M.op x y) (M.op y X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1514 eq16
    | exact resolve eq16 eq1514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1514
  have eq1566 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1318 eq892
    | exact resolve eq892 eq1318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1571 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq1566 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1566
  have eq1578 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq795 eq1571
    | exact resolve eq1571 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795 eq1571
  have eq1691 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (k X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (k X0 X0) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1362 eq711
    | (have j0 := eq711 X0 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq711 eq1362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq1693 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (k (M.op (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1362 eq11
    | (have j0 := eq11 (M.op (σ (M.op x y)) X0) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq1362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1362
  have eq1697 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (k (M.op (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq1693 X0
       have j1 := eq12 (M.op (σ (M.op x y)) X0) (k (M.op (σ (M.op x y)) X0) (σ (M.op x y)))
       grind)
    | (have r₁ := eq1693 (σ (M.op x y))
       have r₂ := eq12 (σ (M.op x y)) (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))
       grind)
    | (have r₁ := eq1693 X0
       have r₂ := eq12 (M.op (σ (M.op x y)) X0) (σ (M.op x y))
       grind)
    | (have r₁ := eq1693 (σ (M.op x y))
       have r₂ := eq12 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1693 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1693
  have eq1698 : ∀ X0 : G, (k X0 (k (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ (M.op x y)) X0) ∨ (k X0 X0) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1691 X0
       have i₂ := eq174 sF1
       grind)
    | exact superpose eq174 eq1691
    | (have j0 := eq1691 X0
       grind)
    | exact resolve eq1691 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1691
  have eq1703 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (k X0 X0) ∨ (k X0 (k (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ (M.op x y)) X0) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1698 X0
       have i₂ := eq174 sF1
       grind)
    | exact superpose eq174 eq1698
    | (have j0 := eq1698 X0
       grind)
    | exact resolve eq1698 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1698
  have eq1706 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = X0 ∨ (k (σ (M.op x y)) (σ (M.op x y))) = (k X0 X0) ∨ (k X0 (k (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ (M.op x y)) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1703 X0
       have i₂ := eq174 sF1
       grind)
    | exact superpose eq174 eq1703
    | (have j0 := eq1703 X0
       grind)
    | exact resolve eq1703 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1703
  have eq1708 : ∀ X0 : G, (σ (M.op x y)) = X0 ∨ (k (σ (M.op x y)) (σ (M.op x y))) = (k X0 X0) ∨ (k X0 (k (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ (M.op x y)) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1308 eq1706
    | (have j0 := eq1706 X0
       grind)
    | exact resolve eq1706 eq1308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1706
  have eq1710 : ∀ X0 : G, (σ (M.op x y)) = X0 ∨ (σ (M.op x y)) = (k X0 X0) ∨ (k X0 (k (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ (M.op x y)) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1308 eq1708
    | (have j0 := eq1708 X0
       grind)
    | exact resolve eq1708 eq1308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1708
  have eq1712 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (k X0 X0) ∨ (σ (M.op x y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1308 eq1710
    | (have j0 := eq1710 X0
       grind)
    | exact resolve eq1710 eq1308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1710
  have eq1806 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1329 eq1578
    | exact resolve eq1578 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1578
  have eq1818 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1806
  have eq1940 : ∀ X0 : G, (M.op y X0) = (k (M.op y X0) (M.op x y)) ∨ (M.op x y) = (M.op (M.op y X0) (M.op y X0)) ∨ (M.op x y) = (M.op y X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1532 eq11
    | (have j0 := eq11 (M.op y X0) (M.op x y)
       grind)
    | exact resolve eq11 eq1532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1532
  have eq1950 : ∀ X0 : G, (M.op y X0) = (k (M.op y X0) (M.op x y)) ∨ (M.op x y) = (M.op y X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq1940 X0
       have j1 := eq12 (M.op y X0) (k (M.op y X0) (M.op x y))
       grind)
    | (have r₁ := eq1940 y
       have r₂ := eq12 y (k (M.op y y) (M.op x y))
       grind)
    | (have r₁ := eq1940 X0
       have r₂ := eq12 (M.op y X0) (M.op x y)
       grind)
    | (have r₁ := eq1940 y
       have r₂ := eq12 y (M.op x y)
       grind)
    | exact resolve eq1940 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1940
  have eq2738 : (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) ∨ (σ y) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1029 eq11
    | (have j0 := eq11 (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)
       grind)
    | exact resolve eq11 eq1029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029
  have eq2745 : (σ y) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) ∨ (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2738
       have i₂ := eq174 (k sF4 sF4)
       grind)
    | exact superpose eq174 eq2738
    | exact resolve eq2738 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2738
  have eq2752 : (σ y) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op (σ y) (M.op (σ x) (σ y))) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) ∨ (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1318 eq2745
    | exact resolve eq2745 eq1318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318 eq2745
  have eq2759 : (σ y) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (k (σ x) (σ x)) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) ∨ (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq906 eq2752
    | exact resolve eq2752 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906 eq2752
  have eq2763 : (σ y) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) ∨ (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1289 eq2759
    | exact resolve eq2759 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2759
  have eq2767 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) ∨ (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1326 eq2763
    | exact resolve eq2763 eq1326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2763
  have eq2768 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2767
  have eq2774 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1326 eq2768
    | exact resolve eq2768 eq1326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2768
  have eq2777 : (σ y) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1326 eq2774
    | exact resolve eq2774 eq1326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2774
  have eq2779 : (τ (σ y)) = (k (τ (M.op (σ x) (σ y))) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2777 eq152
    | exact resolve eq152 eq2777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq2777
  have eq2784 : y = (k (τ (M.op (σ x) (σ y))) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq31 eq2779
    | exact resolve eq2779 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2779
  have eq3699 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1374 eq1326
    | exact resolve eq1326 eq1374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1374
  have eq3704 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3699
  have eq3834 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq899 eq1376
    | exact resolve eq1376 eq899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899 eq1376
  have eq3837 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq3834
  have eq3840 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1329 eq3837
    | exact resolve eq3837 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329 eq3837
  have eq3844 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3704 eq3840
    | exact resolve eq3840 eq3704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3704 eq3840
  have eq3849 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3844
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq3844
    | exact resolve eq3844 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3844
  have eq3850 : (σ x) = (σ y) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1289 eq3849
    | exact resolve eq3849 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3849
  have eq3851 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq3850
  have eq3853 : (τ (σ x)) = (k (τ (M.op (σ x) (σ y))) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3851 eq141
    | exact resolve eq141 eq3851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq3856 : x = (k (τ (M.op (σ x) (σ y))) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq29 eq3853
    | exact resolve eq3853 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3853
  have eq3868 : (k x x) = (k (M.op x y) (k x x)) ∨ (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1466 x
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq1466
    | exact resolve eq1466 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466
  have eq3880 : (M.op x y) = (k x x) ∨ y = (k (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1083 eq3868
    | exact resolve eq3868 eq1083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3868
  have eq3888 : (M.op y (M.op x y)) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq876
       have i₂ := eq3880
       grind)
    | exact superpose eq3880 eq876
    | exact resolve eq876 eq3880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876 eq3880
  have eq3897 : (M.op y (M.op x y)) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k (M.op x y) y) := by grind
  clear eq3888
  have eq3905 : (k x x) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k (M.op x y) y) := by
    first
    | exact superpose eq859 eq3897
    | exact resolve eq3897 eq859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859 eq3897
  have eq3908 : y = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k (M.op x y) y) := by
    first
    | exact superpose eq1083 eq3905
    | exact resolve eq3905 eq1083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083 eq3905
  have eq3911 : x = y ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k (M.op x y) y) := by
    first
    | exact superpose eq1291 eq3908
    | exact resolve eq3908 eq1291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1291 eq3908
  have eq3912 : y = (k (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq3911
  have eq3913 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3912 eq37
    | exact resolve eq37 eq3912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq3912
  have eq3917 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3913
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3913
    | exact resolve eq3913 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3913
  have eq4267 : (k y y) = (k (k y y) (M.op x y)) ∨ (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1950 y
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq1950
    | exact resolve eq1950 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1950
  have eq4287 : (M.op x y) = (k y y) ∨ x = (k x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq760 eq4267
    | exact resolve eq4267 eq760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760 eq4267
  have eq4330 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (k x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq4287
       grind)
    | exact superpose eq4287 eq40
    | exact resolve eq40 eq4287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq4287
  have eq4336 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (k x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4330
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4330
    | exact resolve eq4330 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4330
  have eq4341 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (k x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq4336
    | exact resolve eq4336 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4336
  have eq4344 : x = (k x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq777 eq4341
    | exact resolve eq4341 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4341
  have eq4348 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq4344 eq41
    | exact resolve eq41 eq4344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq4344
  have eq4350 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4348
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4348
    | exact resolve eq4348 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4348
  have eq4356 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op x y)) (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq4350 eq712
    | (have j0 := eq712 (σ x) (σ (M.op x y)) x
       grind)
    | exact resolve eq712 eq4350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712 eq4350
  have eq4357 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op x y)) (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq4356 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4356
  have eq4358 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op x y)) (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1289 eq4357
    | (have j0 := eq4357 X0
       grind)
    | exact resolve eq4357 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4357
  have eq5734 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq4358
    | (have j0 := eq4358 (σ y)
       grind)
    | exact resolve eq4358 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4358
  have eq5778 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq5734 eq1697
    | exact resolve eq1697 eq5734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1697 eq5734
  have eq5784 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq5778
  have eq5791 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq5784
       have r₂ := eq27
       grind)
    | exact resolve eq5784 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5784
  have eq6619 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3917 eq890
    | (have j0 := eq890 (σ (M.op x y))
       grind)
    | exact resolve eq890 eq3917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890
  have eq6655 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq6619
  have eq6664 : (k (σ y) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq6655
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq6655
    | exact resolve eq6655 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6655
  have eq6669 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq777 eq6664
    | exact resolve eq6664 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6664
  have eq6673 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1308 eq6669
    | exact resolve eq6669 eq1308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1308 eq6669
  have eq6674 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6673
  have eq6677 : (M.op (σ y) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq6674 eq892
    | exact resolve eq892 eq6674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892
  have eq6699 : (M.op (σ y) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq6677
  have eq6708 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq896 eq6699
    | exact resolve eq6699 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896 eq6699
  have eq6937 : (M.op y x) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ x = (k (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3856 eq941
    | (have j0 := eq941 (τ (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq941 eq3856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941 eq3856
  have eq6971 : (M.op y x) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ x = (k (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq6937
  have eq6981 : x = (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op y x) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq6971
       have i₂ := eq404 sF4 sF4
       grind)
    | exact superpose eq404 eq6971
    | exact resolve eq6971 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6971
  have eq6988 : x = (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq849 eq6981
    | exact resolve eq6981 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849 eq6981
  have eq6992 : x = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1326 eq6988
    | exact resolve eq6988 eq1326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6988
  have eq6993 : (M.op x y) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6992
  have eq7003 : (M.op x y) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq6993 eq11
    | (have j0 := eq11 (τ (M.op (σ x) (σ y))) (M.op x y)
       grind)
    | exact resolve eq11 eq6993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6993
  have eq7011 : (M.op x y) = (k (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq7003
       have i₂ := eq174 (τ sF4)
       grind)
    | exact superpose eq174 eq7003
    | exact resolve eq7003 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7003
  have eq7020 : (M.op x y) = (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq7011
       have i₂ := eq404 sF4 sF4
       grind)
    | exact superpose eq404 eq7011
    | exact resolve eq7011 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404 eq7011
  have eq7028 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1326 eq7020
    | exact resolve eq7020 eq1326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7020
  have eq7029 : (M.op x y) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq7028
  have eq7221 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq7029 eq34
    | exact resolve eq34 eq7029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq7029
  have eq7228 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq7221
    | exact resolve eq7221 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7221
  have eq7322 : (k (σ x) (σ x)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq6674 eq182
    | exact resolve eq182 eq6674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6674
  have eq7352 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq6708 eq182
    | exact resolve eq182 eq6708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6708
  have eq7755 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1326 eq7352
    | exact resolve eq7352 eq1326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7352
  have eq7782 : (σ y) = (M.op (σ x) (M.op (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1289 eq7322
    | exact resolve eq7322 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7322
  have eq8499 : (k (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (σ (M.op x y)) (σ x)) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq7782 eq182
    | exact resolve eq182 eq7782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7782
  have eq8522 : (k (σ y) (σ y)) = (M.op (σ x) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq8499
       have i₂ := eq16 sF1 sF2 sF3
       grind)
    | exact superpose eq16 eq8499
    | exact resolve eq8499 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8499
  have eq8540 : (k (σ y) (σ y)) = (M.op (σ x) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq8522
    | exact resolve eq8522 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8522
  have eq8552 : (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq777 eq8540
    | exact resolve eq8540 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8540
  have eq8580 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1712 eq7755
    | (have j1 := eq1712 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq7755 eq1712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7755
  have eq8612 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by grind
  clear eq8580
  have eq8629 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq8612
       have r₂ := eq27
       grind)
    | exact resolve eq8612 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8612
  have eq8638 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1326 eq8629
    | exact resolve eq8629 eq1326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8629
  have eq8646 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq8638
       have r₂ := eq27
       grind)
    | exact resolve eq8638 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8638
  have eq8884 : (σ x) = (M.op (σ x) (k (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1712 eq8552
    | (have j1 := eq1712 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq8552 eq1712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1712 eq8552
  have eq8923 : (σ x) = (M.op (σ x) (k (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by grind
  clear eq8884
  have eq8937 : (σ x) = (M.op (σ x) (k (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq8923
       have r₂ := eq27
       grind)
    | exact resolve eq8923 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8923
  have eq8946 : (σ x) = (M.op (σ x) (k (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1326 eq8937
    | exact resolve eq8937 eq1326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8937
  have eq8952 : (σ x) = (M.op (σ x) (k (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq8946
       have r₂ := eq27
       grind)
    | exact resolve eq8946 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8946
  have eq8974 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (k (M.op (σ x) (σ y)) (σ (M.op x y))) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq8646 eq182
    | exact resolve eq182 eq8646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8646
  have eq8988 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (k (M.op (σ x) (σ y)) (σ (M.op x y))) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1326 eq8974
    | exact resolve eq8974 eq1326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8974
  have eq9283 : (k (σ x) (σ x)) = (M.op (σ x) (M.op (k (M.op (σ x) (σ y)) (σ (M.op x y))) (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq8952 eq182
    | exact resolve eq182 eq8952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8952
  have eq9301 : (σ y) = (M.op (σ x) (M.op (k (M.op (σ x) (σ y)) (σ (M.op x y))) (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1289 eq9283
    | exact resolve eq9283 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9283
  have eq9986 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ (M.op x y))))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq8988
       have i₂ := eq11 sF4 (k sF4 sF1)
       grind)
    | exact superpose eq11 eq8988
    | (have j1 := eq11 (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ (M.op x y)))
       grind)
    | exact resolve eq8988 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8988
  have eq10019 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ (M.op x y))))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq9986
       have i₂ := eq174 sF4
       grind)
    | exact superpose eq174 eq9986
    | exact resolve eq9986 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9986
  have eq10026 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ (M.op x y))))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1326 eq10019
    | exact resolve eq10019 eq1326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10019
  have eq10027 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ (M.op x y))))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq10026
  have eq10032 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ x)))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5791 eq10027
    | exact resolve eq10027 eq5791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10027
  have eq10036 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ x))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3851 eq10032
    | exact resolve eq10032 eq3851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10032
  have eq10038 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3851 eq10036
    | exact resolve eq10036 eq3851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3851 eq10036
  have eq10039 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1818 eq10038
    | exact resolve eq10038 eq1818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1818 eq10038
  have eq10084 : (k (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (k (M.op (σ x) (σ y)) (σ (M.op x y))) (σ x)) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq9301 eq182
    | exact resolve eq182 eq9301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq9301
  have eq10104 : (k (σ y) (σ y)) = (M.op (σ x) (M.op (k (M.op (σ x) (σ y)) (σ (M.op x y))) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq10084
       have i₂ := eq16 (k sF4 sF1) sF2 sF3
       grind)
    | exact superpose eq16 eq10084
    | exact resolve eq10084 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10084
  have eq10116 : (k (σ y) (σ y)) = (M.op (σ x) (M.op (k (M.op (σ x) (σ y)) (σ (M.op x y))) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq10104
    | exact resolve eq10104 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10104
  have eq10126 : (σ x) = (M.op (σ x) (M.op (k (M.op (σ x) (σ y)) (σ (M.op x y))) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq777 eq10116
    | exact resolve eq10116 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10116
  have eq10746 : (σ x) = (M.op (σ x) (k (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq10126
       have i₂ := eq11 sF4 (k sF4 sF1)
       grind)
    | exact superpose eq11 eq10126
    | (have j1 := eq11 (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ (M.op x y)))
       grind)
    | exact resolve eq10126 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10126
  have eq10790 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (k (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq10746
       have i₂ := eq174 sF4
       grind)
    | exact superpose eq174 eq10746
    | exact resolve eq10746 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10746
  have eq10801 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (k (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1326 eq10790
    | exact resolve eq10790 eq1326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326 eq10790
  have eq10802 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (k (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq10801
  have eq10810 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (k (σ x) (k (σ x) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq10039 eq10802
    | exact resolve eq10802 eq10039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10039 eq10802
  have eq10816 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (k (σ x) (k (σ x) (σ x)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq5791 eq10810
    | exact resolve eq10810 eq5791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5791 eq10810
  have eq10820 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (k (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1289 eq10816
    | exact resolve eq10816 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10816
  have eq10823 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1300 eq10820
    | exact resolve eq10820 eq1300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1300 eq10820
  have eq10825 : (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq10823
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq10823
    | exact resolve eq10823 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10823
  have eq10826 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1289 eq10825
    | exact resolve eq10825 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1289 eq10825
  have eq10827 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq10826
  have eq10829 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq10827 eq7228
    | exact resolve eq7228 eq10827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7228 eq10827
  have eq10850 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq10829
  have eq10860 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq10850
       have r₂ := eq27
       grind)
    | exact resolve eq10850 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10850
  have eq10925 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq10860 eq14
    | exact resolve eq14 eq10860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10860
  have eq10968 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq10925
    | exact resolve eq10925 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10925
  have eq10986 : x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq10968
       have r₂ := eq27
       grind)
    | exact resolve eq10968 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10968
  have eq11001 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq10986 eq2784
    | exact resolve eq2784 eq10986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2784
  have eq11014 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq10986 eq14
    | exact resolve eq14 eq10986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10986
  have eq11034 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq11001
  have eq11040 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq11014
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11014
    | exact resolve eq11014 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11014
  have eq11044 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1282 eq11034
    | exact resolve eq11034 eq1282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282 eq11034
  have eq11045 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq11044
  have eq11050 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq11040 eq11045
    | exact resolve eq11045 eq11040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11040 eq11045
  have eq11051 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq11050
  have eq11053 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq11051 eq31
    | exact resolve eq31 eq11051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11051
  have eq11088 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq11053
    | exact resolve eq11053 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11053
  have eq11089 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq11088
  have eq11117 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq11089 eq3917
    | exact resolve eq3917 eq11089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3917 eq11089
  have eq11136 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq11117
  have eq11150 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq777 eq11136
    | exact resolve eq11136 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777 eq11136
  have eq11151 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq11150
  have eq11180 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq11151 eq31
    | exact resolve eq31 eq11151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq11151
  have eq11216 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq11180
    | exact resolve eq11180 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq11180
  have eq11217 : x = y := by grind
  clear eq11216
  have eq11235 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11217
       grind)
    | exact superpose eq11217 eq18
    | exact resolve eq18 eq11217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq11236 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq11217
       grind)
    | exact superpose eq11217 eq24
    | exact resolve eq24 eq11217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq11217
  have eq11244 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq11236
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11236
    | exact resolve eq11236 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11236
  have eq11245 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq11235
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq11235
    | exact resolve eq11235 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11235
  have eq11246 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq11244 eq26
    | exact resolve eq26 eq11244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq11244
  have eq11282 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq11246
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq11246
    | exact resolve eq11246 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq11246
  have eq11291 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq11245
       grind)
    | exact superpose eq11245 eq39
    | exact resolve eq39 eq11245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq11245
  have eq11295 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq11291
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11291
    | exact resolve eq11291 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq11291
  have eq11300 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11282 eq11295
    | exact resolve eq11295 eq11282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11282 eq11295
  have eq11302 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq11300
    | exact resolve eq11300 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq11300
  have eq11304 : False := by grind
  exact eq11304
