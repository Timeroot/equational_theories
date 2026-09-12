import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pxy_pxx_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq63 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
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
  have eq64 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
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
  have eq66 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq63 (M.op X1 X0) X0
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq63
    | exact resolve eq63 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq63 (M.op X1 X1) X0
       have i₂ := eq64 X1 X0
       grind)
    | exact superpose eq64 eq63
    | exact resolve eq63 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  clear eq74
  have eq96 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq91 X0
       have i₂ := eq64 X0 (M.op X0 X0)
       grind)
    | exact superpose eq64 eq91
    | exact resolve eq91 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq106 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq120 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq122 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq513 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  clear eq106
  have eq520 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq513 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq513
    | (have j0 := eq513 X0
       grind)
    | exact resolve eq513 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513
  have eq521 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq520 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq529 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq521 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq521
    | exact resolve eq521 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq538 : ∀ X0 X1 : G, (M.op X1 (σ (k X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq64 (σ X0) X1
       have i₂ := eq521 X0
       grind)
    | exact superpose eq521 eq64
    | exact resolve eq64 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq548 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq529 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq529
    | exact resolve eq529 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq529
  have eq550 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq548 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq548
    | exact resolve eq548 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq631 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq538 (M.op X0 X0) X1
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq538
    | exact resolve eq538 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq538
  have eq672 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq63 (σ (M.op X1 X1)) X0
       have i₂ := eq631 X1 X0
       grind)
    | exact superpose eq631 eq63
    | exact resolve eq63 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq631
  have eq689 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq120 x y
       grind)
    | exact superpose eq120 eq16
    | (have j1 := eq120 x y
       grind)
    | exact resolve eq16 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq700 : (σ x) = (σ (k y y)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq689
       have i₂ := eq521 y
       grind)
    | exact superpose eq521 eq689
    | exact resolve eq689 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq709 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq700
       have i₂ := eq550 y
       grind)
    | exact superpose eq550 eq700
    | exact resolve eq700 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq13503 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq122 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq122
    | exact resolve eq122 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq13629 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13503 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq13503
    | (have j0 := eq13503 X0 X1
       grind)
    | exact resolve eq13503 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13503
  have eq41472 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq709
       have i₂ := eq13629 x y
       grind)
    | exact superpose eq13629 eq709
    | (have j1 := eq13629 x y
       grind)
    | (have r₁ := eq709
       have r₂ := eq13629 x y
       grind)
    | (have r₁ := eq709
       have r₂ := eq13629 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq709
       have r₂ := eq13629 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq709 eq13629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709 eq13629
  have eq41473 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq41472
  have eq319617 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq41473
       grind)
    | exact superpose eq41473 eq16
    | exact resolve eq16 eq41473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41473
  have eq319628 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq319617
       have i₂ := eq521 x
       grind)
    | exact superpose eq521 eq319617
    | exact resolve eq319617 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319617
  have eq319629 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq319628
       have i₂ := eq550 x
       grind)
    | exact superpose eq550 eq319628
    | exact resolve eq319628 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319628
  have eq319630 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq319629
  have eq319632 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq319630
       grind)
    | exact superpose eq319630 eq10
    | exact resolve eq10 eq319630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319630
  have eq319837 : x = y ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq319632
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq319632
    | exact resolve eq319632 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319632
  have eq319862 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq319837
       grind)
    | exact superpose eq319837 eq16
    | exact resolve eq16 eq319837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319837
  have eq319873 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq319862
       have i₂ := eq521 x
       grind)
    | exact superpose eq521 eq319862
    | exact resolve eq319862 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521 eq319862
  have eq319874 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq319873
       have i₂ := eq550 x
       grind)
    | exact superpose eq550 eq319873
    | exact resolve eq319873 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550 eq319873
  have eq319875 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq319874
  have eq320068 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq319875
       grind)
    | exact superpose eq319875 eq10
    | exact resolve eq10 eq319875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319875
  have eq320275 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq320068
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq320068
    | exact resolve eq320068 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320068
  have eq320276 : x = (M.op y y) := by grind
  clear eq320275
  have eq320296 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq672 X0 y
       have i₂ := eq320276
       grind)
    | exact superpose eq320276 eq672
    | exact resolve eq672 eq320276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq320878 : x = (M.op x y) := by
    first
    | (have i₁ := eq66 y y
       have i₂ := eq320276
       grind)
    | exact superpose eq320276 eq66
    | exact resolve eq66 eq320276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq320276
  have eq325120 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq320296 (σ y)
       grind)
    | exact superpose eq320296 eq16
    | exact resolve eq16 eq320296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320296
  have eq326026 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq325120
       have i₂ := eq320878
       grind)
    | exact superpose eq320878 eq325120
    | exact resolve eq325120 eq320878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320878 eq325120
  have eq326027 : False := by grind
  exact eq326027

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if X = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyy_pyy_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq65 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
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
  have eq66 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
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
  have eq68 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq65 (M.op X1 X0) X0
       have i₂ := eq65 X0 X1
       grind)
    | exact superpose eq65 eq65
    | exact resolve eq65 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq102 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq116 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq118 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq468 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq471 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq102 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq472 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq468 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq468
    | (have j0 := eq468 X0
       grind)
    | exact resolve eq468 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468
  have eq478 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq472 X0
       have j1 := eq471 X0
       grind)
    | (have r₁ := eq472 X0
       have r₂ := eq471 X0
       grind)
    | exact resolve eq472 eq471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471 eq472
  have eq481 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq478 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq478
    | exact resolve eq478 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq488 : ∀ X0 X1 : G, (M.op X1 (σ (k X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq66 (σ X0) X1
       have i₂ := eq478 X0
       grind)
    | exact superpose eq478 eq66
    | exact resolve eq66 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq498 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq481 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq481
    | exact resolve eq481 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq481
  have eq499 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq498 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq498
    | exact resolve eq498 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq580 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq488 (M.op X0 X0) X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq488
    | exact resolve eq488 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq488
  have eq619 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq65 (σ (M.op X1 X1)) X0
       have i₂ := eq580 X1 X0
       grind)
    | exact superpose eq580 eq65
    | exact resolve eq65 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq580
  have eq705 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq116 x y
       grind)
    | exact superpose eq116 eq16
    | (have j1 := eq116 x y
       grind)
    | exact resolve eq16 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq716 : (σ x) = (σ (k y y)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq705
       have i₂ := eq478 y
       grind)
    | exact superpose eq478 eq705
    | exact resolve eq705 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq725 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq716
       have i₂ := eq499 y
       grind)
    | exact superpose eq499 eq716
    | exact resolve eq716 eq499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq13366 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq118 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq118
    | exact resolve eq118 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq13492 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13366 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq13366
    | (have j0 := eq13366 X0 X1
       grind)
    | exact resolve eq13366 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13366
  have eq41228 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq725
       have i₂ := eq13492 x y
       grind)
    | exact superpose eq13492 eq725
    | (have j1 := eq13492 x y
       grind)
    | (have r₁ := eq725
       have r₂ := eq13492 x y
       grind)
    | (have r₁ := eq725
       have r₂ := eq13492 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq725
       have r₂ := eq13492 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq725 eq13492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725 eq13492
  have eq41229 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq41228
  have eq75824 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq41229
       grind)
    | exact superpose eq41229 eq16
    | exact resolve eq16 eq41229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41229
  have eq75825 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq75824
       have i₂ := eq478 x
       grind)
    | exact superpose eq478 eq75824
    | exact resolve eq75824 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75824
  have eq75826 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq75825
       have i₂ := eq499 x
       grind)
    | exact superpose eq499 eq75825
    | exact resolve eq75825 eq499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75825
  have eq75827 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq75826
  have eq75829 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq75827
       grind)
    | exact superpose eq75827 eq10
    | exact resolve eq10 eq75827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75827
  have eq75909 : x = y ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq75829
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq75829
    | exact resolve eq75829 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75829
  have eq75933 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq75909
       grind)
    | exact superpose eq75909 eq16
    | exact resolve eq16 eq75909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75909
  have eq75934 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq75933
       have i₂ := eq478 x
       grind)
    | exact superpose eq478 eq75933
    | exact resolve eq75933 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478 eq75933
  have eq75935 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq75934
       have i₂ := eq499 x
       grind)
    | exact superpose eq499 eq75934
    | exact resolve eq75934 eq499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499 eq75934
  have eq75936 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq75935
  have eq76438 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq75936
       grind)
    | exact superpose eq75936 eq10
    | exact resolve eq10 eq75936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75936
  have eq76522 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq76438
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq76438
    | exact resolve eq76438 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76438
  have eq76523 : x = (M.op y y) := by grind
  clear eq76522
  have eq76540 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq619 X0 y
       have i₂ := eq76523
       grind)
    | exact superpose eq76523 eq619
    | exact resolve eq619 eq76523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq76750 : x = (M.op x y) := by
    first
    | (have i₁ := eq68 y y
       have i₂ := eq76523
       grind)
    | exact superpose eq76523 eq68
    | exact resolve eq68 eq76523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq76523
  have eq78496 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq76540 (σ y)
       grind)
    | exact superpose eq76540 eq16
    | exact resolve eq16 eq76540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76540
  have eq78853 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq78496
       have i₂ := eq76750
       grind)
    | exact superpose eq76750 eq78496
    | exact resolve eq78496 eq76750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76750 eq78496
  have eq78854 : False := by grind
  exact eq78854

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_x_pyy_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq31 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
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
  have eq32 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
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
  have eq34 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (M.op X1 X0) X0
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq31
    | exact resolve eq31 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq32 X0 (M.op X0 X0)
       grind)
    | exact superpose eq32 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq32 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (M.op X1 X1) X0
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq31
    | exact resolve eq31 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq52 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op X1 X1)
       have i₂ := eq44 X1 (τ X0)
       grind)
    | exact superpose eq44 eq17
    | exact resolve eq17 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq52
    | exact resolve eq52 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq57 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (M.op X1 X1))
       have i₂ := eq53 (τ X0) X1
       grind)
    | exact superpose eq53 eq17
    | exact resolve eq17 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq58 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq57
    | exact resolve eq57 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq89 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (k (τ X0) X1) X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq62
    | (have j0 := eq62 X2 X2
       grind)
    | exact resolve eq62 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X0 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq62
    | exact resolve eq62 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq62 x y
       grind)
    | exact superpose eq62 eq16
    | (have j1 := eq62 x y
       grind)
    | exact resolve eq16 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (M.op X1 (σ (k X0 X0))) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 (σ X0) X1
       have i₂ := eq62 X0 X0
       grind)
    | exact superpose eq62 eq32
    | (have j1 := eq62 X0 X0
       grind)
    | exact resolve eq32 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq62 X0 X0
       grind)
    | exact superpose eq62 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq62 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq62 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq62 X0 X1
       grind)
    | exact resolve eq12 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq62 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq106 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq105 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq108 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq100 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq110 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 (σ (k X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq98 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq115 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq108 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq108 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq108 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq125 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op X1 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (M.op X1 X1)))
       have i₂ := eq58 (τ X0) X1
       grind)
    | exact superpose eq58 eq17
    | exact resolve eq17 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq128 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (M.op X1 X1))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq125 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq125
    | exact resolve eq125 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq129 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq22
  have eq144 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (M.op X1 X1)
       have i₂ := eq44 X1 (σ X0)
       grind)
    | exact superpose eq44 eq28
    | exact resolve eq28 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq157 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq144 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq144
    | exact resolve eq144 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq187 : ∀ X0 X1 : G, (σ (σ (k X0 X0))) ≠ (σ (σ X0)) ∨ (k X1 (σ (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq115 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq115
    | (have j0 := eq115 (σ X0) X1
       grind)
    | exact resolve eq115 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 X1 : G, (σ (σ (σ (σ (M.op X0 X0))))) ≠ (σ (σ (σ (σ (M.op X0 X0))))) ∨ (k X1 (σ (σ (σ (σ (M.op X0 X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq115 (σ (σ (σ (M.op X0 X0)))) X1
       have i₂ := eq128 (σ (σ (σ (M.op X0 X0)))) X0
       grind)
    | exact superpose eq128 eq115
    | (have j0 := eq115 (σ (σ (σ (M.op X0 X0)))) X1
       grind)
    | exact resolve eq115 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq274 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (M.op X0 X0)))))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq272 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq348 : ∀ X0 X1 : G, (σ (σ (σ (σ (σ (M.op X0 X0)))))) ≠ (σ (σ (σ (σ (σ (M.op X0 X0)))))) ∨ (k X1 (σ (σ (σ (σ (σ (M.op X0 X0))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq115 (σ (σ (σ (σ (M.op X0 X0))))) X1
       have i₂ := eq274 X0 (σ (σ (σ (σ (M.op X0 X0)))))
       grind)
    | exact superpose eq274 eq115
    | (have j0 := eq115 (σ (σ (σ (σ (M.op X0 X0))))) X1
       grind)
    | exact resolve eq115 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq354 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (σ (M.op X0 X0))))))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq348 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq439 : ∀ X0 X1 : G, (σ (σ (σ (σ (σ (σ (M.op X0 X0))))))) ≠ (σ (σ (σ (σ (σ (σ (M.op X0 X0))))))) ∨ (k X1 (σ (σ (σ (σ (σ (σ (M.op X0 X0)))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq115 (σ (σ (σ (σ (σ (M.op X0 X0)))))) X1
       have i₂ := eq354 X0 (σ (σ (σ (σ (σ (M.op X0 X0))))))
       grind)
    | exact superpose eq354 eq115
    | (have j0 := eq115 (σ (σ (σ (σ (σ (M.op X0 X0)))))) X1
       grind)
    | exact resolve eq115 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq446 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (σ (σ (M.op X0 X0)))))))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq439 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq606 : ∀ X0 X1 : G, (σ (σ (σ (σ (σ (σ (σ (M.op X0 X0)))))))) ≠ (σ (σ (σ (σ (σ (σ (σ (M.op X0 X0)))))))) ∨ (k X1 (σ (σ (σ (σ (σ (σ (σ (M.op X0 X0))))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq115 (σ (σ (σ (σ (σ (σ (M.op X0 X0))))))) X1
       have i₂ := eq446 X0 (σ (σ (σ (σ (σ (σ (M.op X0 X0)))))))
       grind)
    | exact superpose eq446 eq115
    | (have j0 := eq115 (σ (σ (σ (σ (σ (σ (M.op X0 X0))))))) X1
       grind)
    | exact resolve eq115 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq615 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (σ (σ (σ (M.op X0 X0))))))))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq606 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq634 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq106 (M.op X0 X0)
       have i₂ := eq44 X0 (M.op X0 X0)
       grind)
    | exact superpose eq44 eq106
    | (have j0 := eq106 (M.op X0 X0)
       grind)
    | exact resolve eq106 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq661 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq634 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq734 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 (σ (k (τ X0) (τ X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq110 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq110
    | (have j0 := eq110 (τ X0) X1
       grind)
    | exact resolve eq110 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq767 : ∀ X0 X1 : G, (M.op X1 (k (σ (τ X0)) X0)) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq734 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq734
    | (have j0 := eq734 X0 X1
       grind)
    | exact resolve eq734 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq768 : ∀ X0 X1 : G, (M.op X1 (k X0 X0)) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq767 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq767
    | (have j0 := eq767 X0 X1
       grind)
    | exact resolve eq767 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq1529 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq94
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq94 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq1530 : y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq1529
  have eq1756 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq32 (σ (M.op X0 X0)) X1
       have i₂ := eq661 X0
       grind)
    | exact superpose eq661 eq32
    | exact resolve eq32 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1757 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 (σ (M.op X0 X0))
       have i₂ := eq661 X0
       grind)
    | exact superpose eq661 eq43
    | exact resolve eq43 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq661
  have eq1833 : ∀ X0 X1 : G, (M.op X1 (σ (σ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1756 (σ (M.op X0 X0)) X1
       have i₂ := eq1756 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq1756 eq1756
    | exact resolve eq1756 eq1756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1837 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 (σ (k X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1756 (k X0 X0) X1
       have i₂ := eq768 X0 (k X0 X0)
       grind)
    | exact superpose eq768 eq1756
    | (have j1 := eq768 X0 X1
       grind)
    | exact resolve eq1756 eq768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq1906 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (σ (σ (σ (σ (M.op X0 X0)))))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq446 (σ (σ (M.op X0 X0))) X1
       have i₂ := eq1833 X0 (σ (σ (M.op X0 X0)))
       grind)
    | exact superpose eq1833 eq446
    | exact resolve eq446 eq1833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1833
  have eq2116 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (k X1 (σ X2)) (σ X0)) = (σ (k (k (τ X1) X2) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 (σ X0) (k X1 (σ X2))
       have i₂ := eq89 X1 X2 X0
       grind)
    | exact superpose eq89 eq31
    | (have j1 := eq89 X1 X2 X0
       grind)
    | exact resolve eq31 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq2117 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (k X1 (σ X2)) (σ X0)) = (σ (k (k (τ X1) X2) X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2116 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2116
  have eq2391 : ∀ X0 X1 X2 : G, (M.op X2 (σ (k X0 X0))) = X2 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq1837 X0 X2
       grind)
    | exact superpose eq1837 eq32
    | (have j1 := eq1837 X0 X2
       grind)
    | exact resolve eq32 eq1837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1837
  have eq2531 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 (k X0 (σ X1)) (σ X2)
       have i₂ := eq92 X0 X1 X2
       grind)
    | exact superpose eq92 eq31
    | (have j1 := eq92 X0 X1 X2
       grind)
    | exact resolve eq31 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq2532 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2531 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2531
  have eq2587 : ∀ X0 X1 X2 : G, (M.op X1 (k (σ (τ X0)) X0)) = X1 ∨ (M.op X2 (τ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2391 (τ X0) X2 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq2391
    | (have j0 := eq2391 (k (σ (τ X0)) X0) X1 X2
       grind)
    | exact resolve eq2391 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2391
  have eq2634 : ∀ X0 X1 X2 : G, (M.op X2 (τ X0)) = X2 ∨ (M.op X1 (k X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2587 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2587
    | (have j0 := eq2587 X0 X1 X2
       grind)
    | exact resolve eq2587 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2587
  have eq4340 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X2 (k X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1757 (τ X0) X1
       have i₂ := eq2634 X0 X1 (τ X0)
       grind)
    | exact superpose eq2634 eq1757
    | (have j1 := eq2634 X0 X2 X2
       grind)
    | exact resolve eq1757 eq2634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1757 eq2634
  have eq4359 : ∀ X0 X1 X2 : G, (M.op X2 (k X0 X0)) = X2 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4340 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4340
    | (have j0 := eq4340 X0 X1 X2
       grind)
    | exact resolve eq4340 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4340
  have eq4435 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq4359 X0 (k X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4359
  have eq4436 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq4435 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4435
  have eq4577 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq31 (k X0 X0) X0
       have i₂ := eq4436 X0
       grind)
    | exact superpose eq4436 eq31
    | exact resolve eq31 eq4436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4436
  have eq4612 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ (k X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq4577 (τ X0)
       have i₂ := eq129 X0 X0
       grind)
    | exact superpose eq129 eq4577
    | exact resolve eq4577 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq4577
  have eq17613 : ∀ X0 X1 X2 X3 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (k X2 (σ X3)) (σ X0)) = (σ (k (k (τ X2) X3) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq157 X1 (σ X0)
       have i₂ := eq2117 X0 X2 X3
       grind)
    | exact superpose eq2117 eq157
    | (have j1 := eq2117 X0 X2 X3
       grind)
    | exact resolve eq157 eq2117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq2117
  have eq17663 : ∀ X0 X1 X2 X3 : G, (M.op (k X2 (σ X3)) (σ X0)) = (σ (k (k (τ X2) X3) X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17613 X0 X1 X2 X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17613
    | (have j0 := eq17613 X0 X1 X2 X3
       grind)
    | exact resolve eq17613 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17613
  have eq25477 : y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq31 y x
       have i₂ := eq1530
       grind)
    | exact superpose eq1530 eq31
    | exact resolve eq31 eq1530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1530
  have eq25478 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq25477
  have eq28999 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X2) X0) = (σ (k X2 (k (τ X0) (σ (σ (σ (σ (σ (M.op X1 X1))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2532 X1 (σ (σ (σ (σ (σ (M.op X0 X0)))))) X2
       have i₂ := eq446 X0 X1
       grind)
    | exact superpose eq446 eq2532
    | exact resolve eq2532 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446 eq2532
  have eq29080 : ∀ X0 X2 : G, (M.op (σ X2) X0) = (σ (k X2 (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq28999 X0 x X2
       have i₂ := eq354 x (τ X0)
       grind)
    | exact superpose eq354 eq28999
    | (have j0 := eq28999 X0 x X2
       grind)
    | exact resolve eq28999 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354 eq28999
  have eq29102 : ∀ X0 X2 : G, (M.op X0 X0) = X0 ∨ (k (σ X2) X0) = (M.op (σ X2) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq29080 X0 X2
       have i₂ := eq18 X0 X2
       grind)
    | exact superpose eq18 eq29080
    | (have j0 := eq29080 X0 X2
       grind)
    | exact resolve eq29080 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq29080
  have eq33367 : ∀ X0 X1 X2 : G, (k (σ X2) X0) = (M.op (σ X2) X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44 X0 X1
       have i₂ := eq29102 X0 X2
       grind)
    | exact superpose eq29102 eq44
    | (have j1 := eq29102 X0 X2
       grind)
    | exact resolve eq44 eq29102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq29102
  have eq35834 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33367 X0 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq33367
    | (have j0 := eq33367 X1 X2 X2
       grind)
    | exact resolve eq33367 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36142 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) X1) ∨ (σ X0) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq33367 X1 (σ X0) x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33367
  have eq36481 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq35834 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35834
  have eq36755 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq36481 (M.op X0 X1) X1
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq36481
    | (have j0 := eq36481 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq36481 (M.op X1 X0) X0
       have r₂ := eq34 X0 X1
       grind)
    | exact resolve eq36481 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq36481
  have eq37032 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have j0 := eq36755 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36755
  have eq128923 : ∀ X0 X1 X2 X3 : G, (σ (k (τ X0) X2)) = (M.op (k X0 (σ (σ (σ (σ (σ (σ (σ (σ (M.op X1 X1)))))))))) (σ X2)) ∨ (k X3 X2) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17663 X2 X3 X0 (σ (σ (σ (σ (σ (σ (σ (M.op X1 X1))))))))
       have i₂ := eq615 X1 (τ X0)
       grind)
    | exact superpose eq615 eq17663
    | (have j0 := eq17663 X2 X3 X2 X3
       grind)
    | exact resolve eq17663 eq615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615 eq17663
  have eq129711 : ∀ X0 X2 X3 : G, (σ (k (τ X0) X2)) = (M.op X0 (σ X2)) ∨ (k X3 X2) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq128923 X0 x X2 X3
       have i₂ := eq1906 x X0
       grind)
    | exact superpose eq1906 eq128923
    | (have j0 := eq128923 X0 x X2 X3
       grind)
    | exact resolve eq128923 eq1906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1906 eq128923
  have eq129884 : ∀ X0 X2 X3 : G, (k X0 (σ X2)) = (M.op X0 (σ X2)) ∨ (k X3 X2) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq129711 X0 X2 X3
       have i₂ := eq17 X0 X2
       grind)
    | exact superpose eq17 eq129711
    | (have j0 := eq129711 X0 X2 X3
       grind)
    | exact resolve eq129711 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq129711
  have eq129995 : ∀ X0 X1 X2 : G, (k X2 (τ X0)) = X2 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq129884 X0 (τ X0) x
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq129884
    | (have j0 := eq129884 X0 (τ X0) X2
       grind)
    | exact resolve eq129884 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129884
  have eq130642 : ∀ X0 X1 X2 : G, (σ (σ (τ X0))) ≠ (σ (σ (τ X0))) ∨ (k X1 (σ (σ (τ X0)))) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq187 (τ X0) X1
       have i₂ := eq129995 X0 X2 (τ X0)
       grind)
    | exact superpose eq129995 eq187
    | (have j0 := eq187 (τ X0) X1
       have j1 := eq129995 X0 X2 X2
       grind)
    | exact resolve eq187 eq129995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq129995
  have eq130979 : ∀ X0 X1 X2 : G, (k X1 (σ (σ (τ X0)))) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq130642 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130642
  have eq131137 : ∀ X0 X1 X2 : G, (k X1 (σ X0)) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq130979 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq130979
    | (have j0 := eq130979 X0 X1 X2
       grind)
    | exact resolve eq130979 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130979
  have eq132372 : ∀ X0 X1 X2 : G, (k X2 (τ X0)) = (M.op X2 (τ X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq131137 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq131137
    | (have j0 := eq131137 (τ X0) X1 X2
       grind)
    | exact resolve eq131137 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131137
  have eq136575 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq106 (τ X0)
       have i₂ := eq132372 X0 X1 (τ X0)
       grind)
    | exact superpose eq132372 eq106
    | (have j0 := eq106 (τ X0)
       have j1 := eq132372 X0 X1 x
       grind)
    | exact resolve eq106 eq132372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq132372
  have eq136977 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq136575 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq136575
    | (have j0 := eq136575 X0 X1
       grind)
    | exact resolve eq136575 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136575
  have eq137002 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq136977 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq136977
    | (have j0 := eq136977 X0 X1
       grind)
    | exact resolve eq136977 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136977
  have eq137009 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq137002 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq137002 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq137002 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137002
  have eq137012 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq137009 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq137009
    | (have j0 := eq137009 (σ X0) X1
       grind)
    | exact resolve eq137009 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137009
  have eq147343 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq37032 (σ x) (σ y)
       have i₂ := eq25478
       grind)
    | exact superpose eq25478 eq37032
    | exact resolve eq37032 eq25478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25478 eq37032
  have eq147356 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq36142 y (σ y)
       grind)
    | (have r₁ := eq147343
       have r₂ := eq36142 y (σ y)
       grind)
    | exact resolve eq147343 eq36142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36142 eq147343
  have eq147362 : y = (M.op y y) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq147356
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq147356
    | exact resolve eq147356 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147356
  have eq147420 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ (σ y) = (σ (k y y)) := by
    intro X0
    first
    | (have i₁ := eq137012 y X0
       have i₂ := eq147362
       grind)
    | exact superpose eq147362 eq137012
    | (have j0 := eq137012 y X0
       grind)
    | exact resolve eq137012 eq147362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137012 eq147362
  have eq147429 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (σ y) = (σ (k y y)) := by
    intro X0
    first
    | (have j0 := eq147420 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147420
  have eq147432 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq147429 X0
       have j1 := eq115 y X0
       grind)
    | (have r₁ := eq147429 X0
       have r₂ := eq115 y x
       grind)
    | exact resolve eq147429 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq147429
  have eq147579 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq4612 (σ y)
       have i₂ := eq147432 (σ y)
       grind)
    | exact superpose eq147432 eq4612
    | exact resolve eq4612 eq147432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4612 eq147432
  have eq147925 : y = (M.op y y) := by
    first
    | (have i₁ := eq147579
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq147579
    | exact resolve eq147579 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147579
  have eq148235 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq32 y X0
       have i₂ := eq147925
       grind)
    | exact superpose eq147925 eq32
    | exact resolve eq32 eq147925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq148257 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1756 y X0
       have i₂ := eq147925
       grind)
    | exact superpose eq147925 eq1756
    | exact resolve eq1756 eq147925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1756 eq147925
  have eq150666 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq148257 (σ x)
       grind)
    | exact superpose eq148257 eq16
    | exact resolve eq16 eq148257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148257
  have eq150682 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq150666
       have i₂ := eq148235 x
       grind)
    | exact superpose eq148235 eq150666
    | exact resolve eq150666 eq148235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148235 eq150666
  have eq150683 : False := by grind
  exact eq150683

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pxy_pyy_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
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
  have eq20 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
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
  have eq30 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (M.op X1 X1) X0
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq19
    | exact resolve eq19 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq20 X0 (M.op X0 X0)
       grind)
    | exact superpose eq20 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq20 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq33 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq32
    | exact resolve eq32 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq32
  have eq62 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op X1 X1)
       have i₂ := eq33 X1 (τ X0)
       grind)
    | exact superpose eq33 eq17
    | exact resolve eq17 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq62
    | exact resolve eq62 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq78 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (M.op X1 X1))
       have i₂ := eq66 (τ X0) X1
       grind)
    | exact superpose eq66 eq17
    | exact resolve eq17 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq78
    | exact resolve eq78 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq86 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op X1 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (M.op X1 X1)))
       have i₂ := eq79 (τ X0) X1
       grind)
    | exact superpose eq79 eq17
    | exact resolve eq17 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq87 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (M.op X1 X1))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq86
    | exact resolve eq86 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq94 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq112 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 (M.op X1 X1)
       have i₂ := eq33 X1 (σ X0)
       grind)
    | exact superpose eq33 eq94
    | exact resolve eq94 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq125 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq112 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq112
    | exact resolve eq112 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq130 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69 (k (τ X0) X1) X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq69
    | (have j0 := eq69 X2 X2
       grind)
    | exact resolve eq69 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq69 X0 X0
       grind)
    | exact superpose eq69 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq69 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq69 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq69 X0 X1
       grind)
    | exact resolve eq12 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq155 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq137 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq158 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq155 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq155 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq155 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq232 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (M.op X1 X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (M.op X1 X1))))
       have i₂ := eq87 (τ X0) X1
       grind)
    | exact superpose eq87 eq17
    | exact resolve eq17 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq234 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (M.op X1 X1)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq232 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq232
    | exact resolve eq232 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq302 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (M.op X1 X1))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (σ (M.op X1 X1)))))
       have i₂ := eq234 (τ X0) X1
       grind)
    | exact superpose eq234 eq17
    | exact resolve eq17 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq306 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (σ (M.op X1 X1))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq302 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq302
    | exact resolve eq302 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq385 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (σ (M.op X1 X1)))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (σ (σ (M.op X1 X1))))))
       have i₂ := eq306 (τ X0) X1
       grind)
    | exact superpose eq306 eq17
    | exact resolve eq17 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq389 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (σ (σ (M.op X1 X1)))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq385 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq385
    | exact resolve eq385 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq503 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (σ (σ (M.op X1 X1))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (σ (σ (σ (M.op X1 X1)))))))
       have i₂ := eq389 (τ X0) X1
       grind)
    | exact superpose eq389 eq17
    | exact resolve eq17 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq509 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (σ (σ (σ (M.op X1 X1))))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq503 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq503
    | exact resolve eq503 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq729 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ (M.op X0 X0))) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq158 (M.op X0 X0) X1
       have i₂ := eq33 X0 (M.op X0 X0)
       grind)
    | exact superpose eq33 eq158
    | (have j0 := eq158 (M.op X0 X0) X1
       grind)
    | exact resolve eq158 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq760 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 X0))) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq729 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq777 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq760 X0 X1
       have i₂ := eq66 X1 X0
       grind)
    | exact superpose eq66 eq760
    | exact resolve eq760 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq760
  have eq815 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ (M.op X1 X1)) X0
       have i₂ := eq777 X1 X0
       grind)
    | exact superpose eq777 eq19
    | exact resolve eq19 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq2174 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 (k X0 (σ X1)) (σ X2)
       have i₂ := eq130 X0 X1 X2
       grind)
    | exact superpose eq130 eq19
    | (have j1 := eq130 X0 X1 X2
       grind)
    | exact resolve eq19 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq130
  have eq45550 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (M.op X0 (σ X2)) = (σ (k (k (τ X0) (σ (σ (σ (σ (σ (σ (M.op X1 X1)))))))) X2)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2174 X0 (σ (σ (σ (σ (σ (σ (M.op X1 X1))))))) X2
       have i₂ := eq509 X0 X1
       grind)
    | exact superpose eq509 eq2174
    | (have j0 := eq2174 X0 X1 X2
       grind)
    | exact resolve eq2174 eq509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509 eq2174
  have eq45635 : ∀ X0 X2 : G, (σ (k (τ X0) X2)) = (M.op X0 (σ X2)) ∨ (M.op X0 X0) = X0 ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq45550 X0 x X2
       have i₂ := eq389 (τ X0) x
       grind)
    | exact superpose eq389 eq45550
    | (have j0 := eq45550 X0 x X2
       grind)
    | exact resolve eq45550 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389 eq45550
  have eq45657 : ∀ X0 X2 : G, (k X0 (σ X2)) = (M.op X0 (σ X2)) ∨ (M.op X0 X0) = X0 ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq45635 X0 X2
       have i₂ := eq17 X0 X2
       grind)
    | exact superpose eq17 eq45635
    | (have j0 := eq45635 X0 X2
       grind)
    | exact resolve eq45635 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq45635
  have eq45679 : ∀ X0 X2 : G, (k X0 (σ X2)) = (M.op X0 (σ X2)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X2
    first
    | (have j0 := eq45657 X0 X2
       have j1 := eq12 X0 (σ X2)
       grind)
    | (have r₁ := eq45657 x X2
       have r₂ := eq12 X0 x
       grind)
    | (have r₁ := eq45657 X0 X2
       have r₂ := eq12 X0 (σ X2)
       grind)
    | exact resolve eq45657 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45657
  have eq45687 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq45679 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq45679
    | (have j0 := eq45679 X1 x
       grind)
    | exact resolve eq45679 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45679
  have eq45985 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq45687 X2 X0
       grind)
    | exact superpose eq45687 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq45687 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq45687 X0 X1
       grind)
    | exact resolve eq12 eq45687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45988 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X0 X2) ∨ (k X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33 X0 X1
       have i₂ := eq45687 X2 X0
       grind)
    | exact superpose eq45687 eq33
    | (have j1 := eq45687 X2 X0
       grind)
    | exact resolve eq33 eq45687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq45993 : ∀ X0 X1 X2 : G, (k X1 (τ X0)) = X1 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq125 X1 X0
       have i₂ := eq45687 X2 X0
       grind)
    | exact superpose eq45687 eq125
    | (have j1 := eq45687 X2 X0
       grind)
    | exact resolve eq125 eq45687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq45687
  have eq46036 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq45985 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45985
  have eq47280 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq45988 X0 X2 (τ X1)
       grind)
    | exact superpose eq45988 eq18
    | (have j1 := eq45988 X0 X2 X2
       grind)
    | exact resolve eq18 eq45988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq45988
  have eq51165 : ∀ X0 X1 X2 : G, (k (σ X0) X2) = (M.op (σ X0) X2) ∨ (k X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq45993 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq45993
    | (have j0 := eq45993 (σ X0) X1 X2
       grind)
    | exact resolve eq45993 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45993
  have eq67538 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq46036 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46036
  have eq67539 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq67538 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67538
  have eq71285 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq51165 X0 X2 (σ X1)
       grind)
    | exact superpose eq51165 eq15
    | (have j1 := eq51165 X0 X2 X2
       grind)
    | exact resolve eq15 eq51165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51165
  have eq191141 : ∀ X0 X1 X2 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq47280 X1 (σ X0) X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq47280
    | (have j0 := eq47280 X1 X1 X2
       grind)
    | exact resolve eq47280 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47280
  have eq191849 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq191141 X0 X1 X2
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq191141
    | (have j0 := eq191141 X0 X1 X2
       grind)
    | exact resolve eq191141 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191141
  have eq238686 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq71285 x y X0
       grind)
    | exact superpose eq71285 eq16
    | (have j1 := eq71285 x x X0
       grind)
    | exact resolve eq16 eq71285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71285
  have eq238975 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq238686 X0
       have j1 := eq191849 X0 x X0
       grind)
    | (have r₁ := eq238686 X0
       have r₂ := eq191849 y x x
       grind)
    | exact resolve eq238686 eq191849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191849 eq238686
  have eq239433 : x = (M.op x x) := by
    first
    | (have i₁ := eq67539 x
       have i₂ := eq238975 x
       grind)
    | exact superpose eq238975 eq67539
    | exact resolve eq67539 eq238975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67539 eq238975
  have eq240104 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq30 X0 x
       have i₂ := eq239433
       grind)
    | exact superpose eq239433 eq30
    | exact resolve eq30 eq239433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq240137 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq815 X0 x
       have i₂ := eq239433
       grind)
    | exact superpose eq239433 eq815
    | exact resolve eq815 eq239433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815 eq239433
  have eq250894 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq240137 (σ y)
       grind)
    | exact superpose eq240137 eq16
    | exact resolve eq16 eq240137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240137
  have eq251092 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq250894
       have i₂ := eq240104 y
       grind)
    | exact superpose eq240104 eq250894
    | exact resolve eq250894 eq240104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240104 eq250894
  have eq251093 : False := by grind
  exact eq251093

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
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
  clear eq21 eq33
  have eq45 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq66 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq109 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq66
    | exact resolve eq66 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq128 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
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
  clear eq34
  have eq140 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq128 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq128
    | exact resolve eq128 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq147 : ∀ X0 X1 : G, (σ (k (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq45 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq45
    | exact resolve eq45 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq166 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq105 X0 (τ (M.op X1 X1))
       have i₂ := eq140 (σ X0) X1
       grind)
    | exact superpose eq140 eq105
    | exact resolve eq105 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq174 : ∀ X0 X1 : G, (k X0 (τ (τ (M.op X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq166 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq166
    | exact resolve eq166 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq182 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (M.op X1 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq105 X0 (τ (τ (M.op X1 X1)))
       have i₂ := eq174 (σ X0) X1
       grind)
    | exact superpose eq174 eq105
    | exact resolve eq105 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq190 : ∀ X0 X1 : G, (k X0 (τ (τ (τ (M.op X1 X1))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq182 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq182
    | exact resolve eq182 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq198 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X0 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq71
    | exact resolve eq71 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq270 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (τ (M.op X1 X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq105 X0 (τ (τ (τ (M.op X1 X1))))
       have i₂ := eq190 (σ X0) X1
       grind)
    | exact superpose eq190 eq105
    | exact resolve eq105 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq279 : ∀ X0 X1 : G, (k X0 (τ (τ (τ (τ (M.op X1 X1)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq270 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq270
    | exact resolve eq270 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq355 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (τ (τ (M.op X1 X1))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq105 X0 (τ (τ (τ (τ (M.op X1 X1)))))
       have i₂ := eq279 (σ X0) X1
       grind)
    | exact superpose eq279 eq105
    | exact resolve eq105 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq361 : ∀ X0 X1 : G, (k X0 (τ (τ (τ (τ (τ (M.op X1 X1))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq355 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq355
    | exact resolve eq355 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq450 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (τ (τ (τ (M.op X1 X1)))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq105 X0 (τ (τ (τ (τ (τ (M.op X1 X1))))))
       have i₂ := eq361 (σ X0) X1
       grind)
    | exact superpose eq361 eq105
    | exact resolve eq105 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq456 : ∀ X0 X1 : G, (k X0 (τ (τ (τ (τ (τ (τ (M.op X1 X1)))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq450 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq450
    | exact resolve eq450 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq582 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (τ (τ (τ (τ (τ (M.op X1 X1))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq105 X0 (τ (τ (τ (τ (τ (τ (M.op X1 X1)))))))
       have i₂ := eq456 (σ X0) X1
       grind)
    | exact superpose eq456 eq105
    | exact resolve eq105 eq456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq588 : ∀ X0 X1 : G, (k X0 (τ (τ (τ (τ (τ (τ (τ (M.op X1 X1))))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq582 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq582
    | exact resolve eq582 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq2950 : ∀ X0 X1 : G, (M.op (k (σ (τ X0)) X1) (k (σ (τ X0)) X1)) = (σ (k (τ (k X0 X1)) (τ (k X0 X1)))) ∨ (k (σ (τ X0)) X1) = (M.op (k (σ (τ X0)) X1) (k (σ (τ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq147 (τ X1) X0
       have i₂ := eq109 X0 X1
       grind)
    | exact superpose eq109 eq147
    | (have j0 := eq147 (τ X0) X1
       grind)
    | exact resolve eq147 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq147
  have eq2996 : ∀ X0 X1 : G, (M.op (k (σ (τ X0)) X1) (k (σ (τ X0)) X1)) = (k (σ (τ (k X0 X1))) (k X0 X1)) ∨ (k (σ (τ X0)) X1) = (M.op (k (σ (τ X0)) X1) (k (σ (τ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2950 X0 X1
       have i₂ := eq19 (k X0 X1) (τ (k X0 X1))
       grind)
    | exact superpose eq19 eq2950
    | (have j0 := eq2950 X0 X1
       grind)
    | exact resolve eq2950 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2950
  have eq3010 : ∀ X0 X1 : G, (M.op (k (σ (τ X0)) X1) (k (σ (τ X0)) X1)) = (k (k X0 X1) (k X0 X1)) ∨ (k (σ (τ X0)) X1) = (M.op (k (σ (τ X0)) X1) (k (σ (τ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2996 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2996
    | (have j0 := eq2996 X0 X1
       grind)
    | exact resolve eq2996 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2996
  have eq3024 : ∀ X0 X1 : G, (k (k X0 X1) (k X0 X1)) = (M.op (k X0 X1) (k X0 X1)) ∨ (k (σ (τ X0)) X1) = (M.op (k (σ (τ X0)) X1) (k (σ (τ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3010 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3010
    | (have j0 := eq3010 X0 X1
       grind)
    | exact resolve eq3010 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3010
  have eq3027 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) (k X0 X1)) ∨ (k (k X0 X1) (k X0 X1)) = (M.op (k X0 X1) (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3024 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3024
    | (have j0 := eq3024 X0 X1
       grind)
    | exact resolve eq3024 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3024
  have eq3028 : ∀ X0 X1 : G, (k (k X0 X1) (k X0 X1)) = (M.op (k X0 X1) (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3027 X0 X1
       have j1 := eq12 (k X0 X1) (k X0 X1)
       grind)
    | (have r₁ := eq3027 X0 X1
       have r₂ := eq12 X0 (k X0 X1)
       grind)
    | exact resolve eq3027 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3027
  have eq3429 : ∀ X0 X1 X2 : G, (k X0 (σ (k X1 (τ X2)))) = (M.op (σ (τ X0)) (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) ∨ (k (σ X1) X2) = (M.op (k (σ X1) X2) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (k X1 (τ X2))
       have i₂ := eq198 X1 X2 (τ X0)
       grind)
    | exact superpose eq198 eq18
    | (have j1 := eq198 X1 X2 (τ X0)
       grind)
    | exact resolve eq18 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq198
  have eq3462 : ∀ X0 X1 X2 : G, (k X0 (σ (k X1 (τ X2)))) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) ∨ (k (σ X1) X2) = (M.op (k (σ X1) X2) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3429 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3429
    | (have j0 := eq3429 X0 X1 X2
       grind)
    | exact resolve eq3429 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3429
  have eq3480 : ∀ X0 X1 X2 : G, (k X0 (k (σ X1) X2)) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) ∨ (k (σ X1) X2) = (M.op (k (σ X1) X2) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3462 X0 X1 X2
       have i₂ := eq19 X2 X1
       grind)
    | exact superpose eq19 eq3462
    | (have j0 := eq3462 X0 X1 X2
       grind)
    | exact resolve eq3462 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3462
  have eq3493 : ∀ X0 X1 X2 : G, (k X0 (k (σ X1) X2)) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3480 X0 X1 X2
       have j1 := eq12 X0 (k (σ X1) X2)
       grind)
    | (have r₁ := eq3480 X0 X1 X2
       have r₂ := eq12 X0 (k (σ X1) X2)
       grind)
    | exact resolve eq3480 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3480
  have eq3505 : ∀ X0 X1 X2 : G, (k X0 (k (σ X1) X2)) = (M.op X0 (k (σ X1) X2)) ∨ (k (σ X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3493 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3493
    | (have j0 := eq3493 X0 X1 X2
       grind)
    | exact resolve eq3493 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3493
  have eq8432 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3505 X0 X1 (τ (τ (τ (τ (τ (τ (M.op X1 X1)))))))
       have i₂ := eq456 (σ X1) X1
       grind)
    | exact superpose eq456 eq3505
    | exact resolve eq3505 eq456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456 eq3505
  have eq8488 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8432 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8432
    | exact resolve eq8432 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8533 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq8432 X1 (σ X0)
       grind)
    | exact superpose eq8432 eq15
    | (have j1 := eq8432 (k X0 X1) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq8432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8432
  have eq8618 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq8488 (τ X1) X0
       grind)
    | exact superpose eq8488 eq19
    | (have j1 := eq8488 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq8488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq8488
  have eq31188 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8618 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8618
    | exact resolve eq8618 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8618
  have eq31369 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31188 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq31188
    | (have j0 := eq31188 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq31188 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31188
  have eq37185 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3028 X0 (τ (τ (τ (τ (τ (τ (τ (M.op x x))))))))
       have i₂ := eq588 X0 x
       grind)
    | exact superpose eq588 eq3028
    | exact resolve eq3028 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588 eq3028
  have eq37728 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq37185 (σ X0)
       grind)
    | exact superpose eq37185 eq15
    | exact resolve eq15 eq37185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37782 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37728 X0
       have i₂ := eq37185 X0
       grind)
    | exact superpose eq37185 eq37728
    | exact resolve eq37728 eq37185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37185 eq37728
  have eq96290 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8533 x y
       grind)
    | exact superpose eq8533 eq16
    | (have j1 := eq8533 x y
       grind)
    | exact resolve eq16 eq8533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8533
  have eq96530 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq96290
       have i₂ := eq31369 y x
       grind)
    | exact superpose eq31369 eq96290
    | (have j1 := eq31369 (σ x) (σ y)
       grind)
    | (have r₁ := eq96290
       have r₂ := eq31369 y x
       grind)
    | (have r₁ := eq96290
       have r₂ := eq31369 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq96290
       have r₂ := eq31369 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq96290 eq31369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31369 eq96290
  have eq96534 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq96530
  have eq97031 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq96534
       grind)
    | exact superpose eq96534 eq16
    | exact resolve eq16 eq96534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96534
  have eq97036 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq97031
       have r₂ := eq37782 x
       grind)
    | exact resolve eq97031 eq37782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97031
  have eq97037 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq97036
       grind)
    | exact superpose eq97036 eq16
    | exact resolve eq16 eq97036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97038 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq97036
       grind)
    | exact superpose eq97036 eq10
    | exact resolve eq10 eq97036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97036
  have eq97290 : x = y := by
    first
    | (have i₁ := eq97038
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq97038
    | exact resolve eq97038 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97038
  have eq97291 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq97037
       have i₂ := eq37782 x
       grind)
    | exact superpose eq37782 eq97037
    | exact resolve eq97037 eq37782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37782 eq97037
  have eq97314 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq97291
       have i₂ := eq97290
       grind)
    | exact superpose eq97290 eq97291
    | exact resolve eq97291 eq97290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97290 eq97291
  have eq97315 : False := by grind
  exact eq97315

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_x_pxx_x_pxy_Equation434 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ X0 = X1 := by
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
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (M.op (σ X0) (σ X0))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq75
    | (have j0 := eq75 X0 X1
       grind)
    | exact resolve eq75 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq82 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) X1) := by
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
  have eq108 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq77 x y
       grind)
    | exact superpose eq77 eq16
    | (have j1 := eq77 x (M.op x x)
       grind)
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq1958 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq108
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq108
    | (have j1 := eq14 x (M.op x x)
       grind)
    | (have r₁ := eq108
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq108
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq108 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq1959 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq1958
  have eq13827 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1959
       grind)
    | exact superpose eq1959 eq16
    | exact resolve eq16 eq1959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1959
  have eq13828 : (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq13827
       have r₂ := eq22 x
       grind)
    | exact resolve eq13827 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13827
  have eq24024 : y = (τ (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq13828
       grind)
    | exact superpose eq13828 eq10
    | exact resolve eq10 eq13828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13828
  have eq24077 : x = y ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq24024
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq24024
    | exact resolve eq24024 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24024
  have eq24079 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24077
       grind)
    | exact superpose eq24077 eq16
    | exact resolve eq16 eq24077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24077
  have eq24080 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq24079
       have r₂ := eq22 x
       grind)
    | exact resolve eq24079 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq24079
  have eq24432 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq24080
       grind)
    | exact superpose eq24080 eq10
    | exact resolve eq10 eq24080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24080
  have eq24494 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq24432
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq24432
    | exact resolve eq24432 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24432
  have eq24495 : x = (M.op x x) := by grind
  clear eq24494
  have eq24501 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq53 X0 x
       have i₂ := eq24495
       grind)
    | exact superpose eq24495 eq53
    | exact resolve eq53 eq24495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq24503 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq82 x x
       have i₂ := eq24495
       grind)
    | exact superpose eq24495 eq82
    | exact resolve eq82 eq24495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq24495
  have eq26518 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24503 (σ y)
       grind)
    | exact superpose eq24503 eq16
    | exact resolve eq16 eq24503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24503
  have eq26702 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq26518
       have i₂ := eq24501 y
       grind)
    | exact superpose eq24501 eq26518
    | exact resolve eq26518 eq24501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24501 eq26518
  have eq26703 : False := by grind
  exact eq26703

/-- `Equation4393`: `x ◇ (x ◇ x) = (y ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then Y else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_y_pxx_pyx_Equation4393 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4393 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4393.models_iff G M).mp hM
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X2) X2) := by
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
  have eq175 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X3 X4) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq16 x X3 X4
       have i₂ := eq16 x X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X3 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X0 (M.op X0 X0)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 X1 (M.op x X3) X3
       have i₂ := eq16 X0 x X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op x y) y) := by
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
  have eq179 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X1 X3 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X3) := by
    intro X1 X3
    first
    | (have i₁ := eq177 x X1 X3
       have i₂ := eq179 x
       grind)
    | exact superpose eq179 eq177
    | exact resolve eq177 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq183 : ∀ X3 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X3) := by
    intro X3
    first
    | (have i₁ := eq181 x X3
       have i₂ := eq179 x
       grind)
    | exact superpose eq179 eq181
    | exact resolve eq181 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq185 : (σ (M.op y y)) = (k (σ y) (σ (M.op y y))) := by
    first
    | (have i₁ := eq36 (M.op y y)
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq36
    | exact resolve eq36 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq188 : ∀ X1 X2 : G, (M.op (M.op X1 X2) X2) = (M.op (M.op x y) y) := by
    intro X1 X2
    first
    | (have i₁ := eq16 x X1 X2
       have i₂ := eq178 x
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq178 x
       have i₂ := eq179 x
       grind)
    | exact superpose eq179 eq178
    | exact resolve eq178 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq179
  have eq202 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq193 eq183
    | exact resolve eq183 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq183 eq174
    | exact resolve eq174 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq219 : (M.op (M.op x y) y) = (k (M.op (M.op x y) y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq193 eq209
    | exact resolve eq209 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq243 : (τ (M.op (σ x) (σ x))) = (k x (τ (M.op (σ x) (σ x)))) := by
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
  have eq254 : (τ (M.op (σ y) (σ y))) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq107 (M.op sF3 sF3)
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq107
    | exact resolve eq107 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq174
  have eq876 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
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
  have eq884 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq959 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq1950 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq876
       grind)
    | exact superpose eq876 eq39
    | exact resolve eq39 eq876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq1951 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1950
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1950
    | exact resolve eq1950 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1950
  have eq1953 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq1951
    | exact resolve eq1951 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1951
  have eq15356 : (σ (M.op (M.op x y) y)) ≠ (σ (M.op (M.op x y) y)) ∨ (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq219 eq959
    | (have j0 := eq959 (M.op (M.op x y) y)
       grind)
    | exact resolve eq959 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq15392 : (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by grind
  clear eq15356
  have eq15518 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    intro X0 X1
    first
    | exact superpose eq15392 eq175
    | exact resolve eq175 eq15392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq15524 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (σ (M.op (M.op x y) y)) := by
    intro X0 X1
    first
    | exact superpose eq15392 eq15518
    | exact resolve eq15518 eq15392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15392 eq15518
  have eq15537 : (M.op (M.op x y) y) = (σ (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq15524 x x
       have i₂ := eq188 x x
       grind)
    | (have i₁ := eq15524 x y
       have i₂ := eq188 x x
       grind)
    | exact superpose eq188 eq15524
    | (have j0 := eq15524 x y
       grind)
    | exact resolve eq15524 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15524
  have eq15554 : (M.op (M.op x y) y) = (τ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq15537 eq15
    | exact resolve eq15 eq15537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15757 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1953 eq884
    | exact resolve eq884 eq1953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1953
  have eq15764 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq15757
       have r₂ := eq27
       grind)
    | exact resolve eq15757 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15757
  have eq15771 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15764 eq254
    | exact resolve eq254 eq15764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254 eq15764
  have eq15800 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq15771
    | exact resolve eq15771 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15771
  have eq15810 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq15800
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq15800
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq15800
       have r₂ := eq13 y x
       grind)
    | exact resolve eq15800 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15800
  have eq15814 : (τ (σ x)) = (k x (τ (σ x))) ∨ x = (k y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq15810 eq243
    | exact resolve eq243 eq15810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243 eq15810
  have eq15842 : x = (k x x) ∨ x = (k y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq15814
    | exact resolve eq15814 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15814
  have eq15852 : x = (k y x) ∨ x = (k x x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq15842
       have r₂ := eq13 x x
       grind)
    | exact resolve eq15842 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15842
  have eq15857 : x = (M.op x y) ∨ x = (k x x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq15852
       have i₂ := eq876
       grind)
    | exact superpose eq876 eq15852
    | exact resolve eq15852 eq876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15860 : x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq876
       have i₂ := eq15852
       grind)
    | exact superpose eq15852 eq876
    | exact resolve eq876 eq15852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876 eq15852
  have eq15865 : x = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq891 x
       grind)
    | (have r₁ := eq15860
       have r₂ := eq891 x
       grind)
    | exact resolve eq15860 eq891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891 eq15860
  have eq15868 : x = (k x x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq15857
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq15857
       have r₂ := eq13 y x
       grind)
    | exact resolve eq15857 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15857
  have eq15902 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq188 y y
       have i₂ := eq15865
       grind)
    | exact superpose eq15865 eq188
    | exact resolve eq188 eq15865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15865
  have eq15907 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15902
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15902
    | exact resolve eq15902 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15902
  have eq15933 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq959 x
       have i₂ := eq15868
       grind)
    | exact superpose eq15868 eq959
    | (have j0 := eq959 x
       grind)
    | exact resolve eq959 eq15868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959 eq15868
  have eq15941 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq15933
  have eq15942 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq15941
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15941
    | exact resolve eq15941 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15941
  have eq16028 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15907 eq15537
    | exact resolve eq15537 eq15907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15907
  have eq16037 : x = (M.op x x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq16028
    | exact resolve eq16028 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16028
  have eq16057 : (M.op (M.op x y) y) = (M.op x x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq188 x x
       have i₂ := eq16037
       grind)
    | exact superpose eq16037 eq188
    | exact resolve eq188 eq16037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16062 : x = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16037 eq16057
    | exact resolve eq16057 eq16037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16037 eq16057
  have eq16119 : x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16062 eq188
    | exact resolve eq188 eq16062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16062
  have eq16124 : x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16119
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16119
    | exact resolve eq16119 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16119
  have eq16125 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq16124
  have eq16133 : (M.op x y) = (τ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16125 eq28
    | exact resolve eq28 eq16125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq17088 : (M.op (M.op x y) y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15942 eq188
    | exact resolve eq188 eq15942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17093 : (σ x) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15942 eq17088
    | exact resolve eq17088 eq15942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15942 eq17088
  have eq18508 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq17093 eq202
    | exact resolve eq202 eq17093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18513 : (σ x) = (τ (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17093 eq15554
    | exact resolve eq15554 eq17093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15554 eq17093
  have eq18538 : x = (M.op y y) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq29 eq18513
    | exact resolve eq18513 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18513
  have eq18566 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq188 y y
       have i₂ := eq18538
       grind)
    | exact superpose eq18538 eq188
    | exact resolve eq188 eq18538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18538
  have eq18571 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq18566
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18566
    | exact resolve eq18566 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18566
  have eq18609 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq18571 eq202
    | exact resolve eq202 eq18571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18571
  have eq20266 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18508 eq26
    | (have j1 := eq18508 (σ y)
       grind)
    | exact resolve eq26 eq18508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20326 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq185
       have i₂ := eq20266
       grind)
    | exact superpose eq20266 eq185
    | exact resolve eq185 eq20266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq20342 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq188 y y
       have i₂ := eq20266
       grind)
    | exact superpose eq20266 eq188
    | exact resolve eq188 eq20266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20266
  have eq20348 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20342
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20342
    | exact resolve eq20342 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20342
  have eq20357 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20326
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20326
    | exact resolve eq20326 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20326
  have eq20418 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20357 eq884
    | exact resolve eq884 eq20357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884 eq20357
  have eq20422 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq20418
  have eq34455 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20422 eq188
    | exact resolve eq188 eq20422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20422
  have eq34468 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq34455
    | exact resolve eq34455 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34455
  have eq34483 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20348 eq34468
    | exact resolve eq34468 eq20348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34468
  have eq34527 : (M.op (M.op x y) y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq34483 eq188
    | exact resolve eq188 eq34483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34539 : (σ x) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq34483 eq34527
    | exact resolve eq34527 eq34483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34483 eq34527
  have eq34552 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20348 eq34539
    | exact resolve eq34539 eq20348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20348 eq34539
  have eq34755 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq34552 eq193
    | exact resolve eq193 eq34552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq34759 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq34755
    | exact resolve eq34755 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34755
  have eq34762 : (σ x) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq34552 eq34759
    | exact resolve eq34759 eq34552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34552 eq34759
  have eq34917 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq34762 eq18609
    | exact resolve eq18609 eq34762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18609
  have eq34934 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (σ x) ∨ (M.op x y) = (σ x) := by grind
  clear eq34917
  have eq35012 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (σ x) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq34934 eq27
    | exact resolve eq27 eq34934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34934
  have eq35014 : (M.op x y) = (σ x) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq35012
       have r₂ := eq16125
       grind)
    | exact resolve eq35012 eq16125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35012
  have eq35018 : x = (τ (M.op x y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35014 eq29
    | exact resolve eq29 eq35014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq35014
  have eq35206 : x = (M.op x y) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16133 eq35018
    | exact resolve eq35018 eq16133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16133 eq35018
  have eq35207 : x = (σ x) ∨ x = (M.op x y) := by grind
  clear eq35206
  have eq35251 : (M.op x y) = (M.op (σ x) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq35207
       grind)
    | exact superpose eq35207 eq18
    | exact resolve eq18 eq35207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35304 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) := by grind
  have eq35557 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35251 eq18508
    | exact resolve eq18508 eq35251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18508
  have eq35563 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq35557
  have eq35568 : x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq35563
       have r₂ := eq35304
       grind)
    | exact resolve eq35563 eq35304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35563
  have eq35578 : (σ x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35207 eq35568
    | exact resolve eq35568 eq35207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35207 eq35568
  have eq35639 : (M.op (M.op x y) y) = (M.op (σ x) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq188 y y
       have i₂ := eq35578
       grind)
    | exact superpose eq35578 eq188
    | exact resolve eq188 eq35578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq35578
  have eq35660 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35251 eq35639
    | exact resolve eq35639 eq35251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35251 eq35639
  have eq35729 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35660 eq34762
    | exact resolve eq34762 eq35660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34762 eq35660
  have eq35736 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq35729
  have eq35743 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq35736
       have r₂ := eq35304
       grind)
    | exact resolve eq35736 eq35304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35304 eq35736
  have eq35765 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35743 eq27
    | exact resolve eq27 eq35743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35743
  have eq35772 : x = (M.op x y) := by
    first
    | (have r₁ := eq35765
       have r₂ := eq16125
       grind)
    | exact resolve eq35765 eq16125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16125 eq35765
  have eq35774 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq35772
       grind)
    | exact superpose eq35772 eq18
    | exact resolve eq18 eq35772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq35775 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq35772
       grind)
    | exact superpose eq35772 eq22
    | exact resolve eq22 eq35772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq35772
  have eq36262 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq35774 eq202
    | exact resolve eq202 eq35774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq36267 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq35774 eq15537
    | exact resolve eq15537 eq35774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15537 eq35774
  have eq36295 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq36267 eq35775
    | exact resolve eq35775 eq36267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35775
  have eq36296 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq36267 eq20
    | exact resolve eq20 eq36267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq36267
  have eq36580 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq36295 eq26
    | exact resolve eq26 eq36295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq36295
  have eq36750 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36262 eq36580
    | exact resolve eq36580 eq36262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36262 eq36580
  have eq36967 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq36750 eq27
    | exact resolve eq27 eq36750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq36750
  have eq36974 : False := by grind
  exact eq36974

/-- `Equation4401`: `x ◇ (x ◇ y) = (x ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(X,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_y_pyx_pxx_pyx_Equation4401 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4401 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4401.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
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
  have eq116 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq48 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 y
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq48
    | (have j0 := eq48 (M.op x y)
       grind)
    | exact resolve eq48 eq20
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
  have eq175 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) X0) = (M.op X0 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 X0 (M.op X0 x) X3
       have i₂ := eq16 X0 x X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq180 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have i₁ := eq16 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x X0 y
       grind)
    | exact resolve eq16 eq18
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
  have eq187 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op (k X0 X1) X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq189 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (k (M.op X0 X1) X0) ∨ (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq28 (M.op X0 X1) X0
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 (M.op X0 X1) X0
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : (M.op x y) = (k y x) ∨ x = (M.op y x) := by
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
  have eq192 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
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
  have eq193 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : (M.op (M.op x y) x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq180 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq180
    | (have j0 := eq180 y
       grind)
    | exact resolve eq180 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq215 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq181
    | (have j0 := eq181 (σ y)
       grind)
    | exact resolve eq181 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq181 eq181
    | exact resolve eq181 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq525 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq191
       grind)
    | exact superpose eq191 eq40
    | exact resolve eq40 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq526 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq525
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq525
    | exact resolve eq525 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525
  have eq528 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq526
    | exact resolve eq526 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq617 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq528 eq192
    | exact resolve eq192 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq624 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq617
       have r₂ := eq27
       grind)
    | exact resolve eq617 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617
  have eq629 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq624 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq630 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq624 eq16
    | exact resolve eq16 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq631 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq26 eq630
    | (have j0 := eq630 X0
       grind)
    | exact resolve eq630 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq632 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq629
    | exact resolve eq629 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq634 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq624 eq631
    | exact resolve eq631 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq635 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq631 eq631
    | exact resolve eq631 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq640 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X1) (σ y)) ∨ x = (M.op y x) := by
    intro X1
    first
    | exact superpose eq631 eq16
    | exact resolve eq16 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq642 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq631 eq16
    | exact resolve eq16 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq644 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op y x) := by grind
  clear eq635
  have eq645 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq634
  have eq646 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq631 eq642
    | exact resolve eq642 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq648 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq624 eq645
    | exact resolve eq645 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq650 : x = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq648
       grind)
    | exact superpose eq648 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq651 : ∀ X0 : G, (M.op x y) = (M.op y (M.op y X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 x
       have i₂ := eq648
       grind)
    | exact superpose eq648 eq16
    | exact resolve eq16 eq648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq652 : ∀ X0 : G, (M.op x y) = (M.op y (M.op y X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq651 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq651
    | (have j0 := eq651 X0
       grind)
    | exact resolve eq651 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq653 : x = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq650
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq650
    | exact resolve eq650 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq657 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq644 eq28
    | (have j0 := eq28 (M.op (σ x) (σ y)) (σ y)
       grind)
    | exact resolve eq28 eq644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq661 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq648 eq657
    | exact resolve eq657 eq648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq663 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq632 eq661
    | exact resolve eq661 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq676 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq679 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (M.op (σ y) X0) (σ y)) = (k (σ y) (M.op (σ y) X0)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq631 eq13
    | (have j0 := eq13 (σ y) (M.op (σ y) X0)
       grind)
    | exact resolve eq13 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq680 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (M.op (σ x) (σ y)) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq644 eq13
    | (have j0 := eq13 (σ y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq13 eq644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq682 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq684 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op (M.op (σ x) (σ y)) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq680
       have i₂ := eq682 sF3
       grind)
    | exact superpose eq682 eq680
    | exact resolve eq680 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680
  have eq685 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op (M.op (σ y) X0) (σ y)) = (k (σ y) (M.op (σ y) X0)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq679 X0
       have i₂ := eq682 sF3
       grind)
    | exact superpose eq682 eq679
    | (have j0 := eq679 X0
       grind)
    | exact resolve eq679 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq688 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq676
       have i₂ := eq682 sF2
       grind)
    | exact superpose eq682 eq676
    | exact resolve eq676 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676
  have eq694 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq646 eq684
    | exact resolve eq684 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646 eq684
  have eq695 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ y) X0)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq640 eq685
    | exact resolve eq685 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq700 : (σ x) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq648 eq694
    | exact resolve eq694 eq648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq701 : ∀ X0 : G, (σ x) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ y) X0)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq648 eq695
    | (have j0 := eq695 X0
       grind)
    | exact resolve eq695 eq648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq705 : (σ x) ≠ (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq648 eq700
    | exact resolve eq700 eq648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq706 : ∀ X0 : G, (σ x) ≠ (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (M.op (σ y) X0)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq648 eq701
    | exact resolve eq701 eq648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq709 : (σ x) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq528 eq705
    | exact resolve eq705 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq723 : x ≠ x ∨ x = (M.op y y) ∨ (k y x) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq648
       grind)
    | exact superpose eq648 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq648
       grind)
    | exact resolve eq12 eq648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq724 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq727 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq624 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq624
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq624
       grind)
    | exact resolve eq12 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq733 : (σ x) = (M.op (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq727
  have eq735 : x = (M.op y y) ∨ (k y x) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq723
  have eq741 : (σ x) = (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq733
       have i₂ := eq682 sF3
       grind)
    | exact superpose eq682 eq733
    | exact resolve eq733 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq744 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq724
       have i₂ := eq682 sF2
       grind)
    | exact superpose eq682 eq724
    | exact resolve eq724 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq745 : x = (k y y) ∨ (k y x) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq735
       have i₂ := eq682 y
       grind)
    | exact superpose eq682 eq735
    | exact resolve eq735 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq760 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq741
       have i₂ := eq682 sF3
       grind)
    | exact superpose eq682 eq741
    | exact resolve eq741 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq763 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq744
       have i₂ := eq682 sF2
       grind)
    | exact superpose eq682 eq744
    | exact resolve eq744 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq764 : (k y x) = (k y y) ∨ x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq745
       have i₂ := eq682 y
       grind)
    | exact superpose eq682 eq745
    | exact resolve eq745 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745
  have eq778 : (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq528 eq760
    | exact resolve eq760 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528 eq760
  have eq791 : (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq652 x
       have i₂ := eq648
       grind)
    | exact superpose eq648 eq652
    | exact resolve eq652 eq648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq792 : (M.op x y) = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq652 (M.op y x)
       have i₂ := eq652 x
       grind)
    | exact superpose eq652 eq652
    | exact resolve eq652 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq797 : ∀ X1 : G, (M.op x y) = (M.op (M.op y X1) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq16 y x X1
       have i₂ := eq652 x
       grind)
    | exact superpose eq652 eq16
    | exact resolve eq16 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq800 : ∀ X0 : G, (M.op x y) = (k (M.op y X0) y) ∨ y = (M.op (M.op y X0) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq28 (M.op y X0) y
       have i₂ := eq652 X0
       grind)
    | exact superpose eq652 eq28
    | (have j0 := eq28 (M.op y X0) y
       grind)
    | exact resolve eq28 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq801 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 (M.op y x)
       have i₂ := eq652 x
       grind)
    | exact superpose eq652 eq16
    | exact resolve eq16 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq802 : ∀ X1 : G, (M.op y (M.op x y)) = (M.op (M.op y X1) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq16 y (M.op y x) X1
       have i₂ := eq652 x
       grind)
    | exact superpose eq652 eq16
    | exact resolve eq16 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq803 : (M.op x y) = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq792
  have eq804 : (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq791
  have eq805 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq652 eq801
    | exact resolve eq801 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq825 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq648
       have i₂ := eq804
       grind)
    | exact superpose eq804 eq648
    | exact resolve eq648 eq804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804
  have eq831 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq825
  have eq845 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq831 eq27
    | exact resolve eq27 eq831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq855 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq805 eq16
    | exact resolve eq16 eq805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq856 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq855 X0
       have i₂ := eq682 sF0
       grind)
    | exact superpose eq682 eq855
    | exact resolve eq855 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq883 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq653
       grind)
    | exact superpose eq653 eq41
    | exact resolve eq41 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq884 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq883
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq883
    | exact resolve eq883 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883
  have eq971 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq856 eq856
    | exact resolve eq856 eq856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq982 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq971
  have eq1041 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq632 eq153
    | exact resolve eq153 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq1042 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq30 eq1041
    | exact resolve eq1041 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041
  have eq1045 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq648 eq1042
    | exact resolve eq1042 eq648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042
  have eq1050 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1045
       grind)
    | exact superpose eq1045 eq41
    | exact resolve eq41 eq1045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1051 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1050
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1050
    | exact resolve eq1050 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1050
  have eq1161 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq778 eq709
    | (have r₁ := eq709
       have r₂ := eq778
       grind)
    | exact resolve eq709 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq1167 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq1161
  have eq1168 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq1167
  have eq1177 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 X0
       have i₂ := eq682 X0
       grind)
    | exact superpose eq682 eq16
    | exact resolve eq16 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1178 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op X0 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X0 X1
       have i₂ := eq682 X0
       grind)
    | exact superpose eq682 eq16
    | exact resolve eq16 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1183 : (M.op x y) = (M.op (k y y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq797 y
       have i₂ := eq682 y
       grind)
    | exact superpose eq682 eq797
    | exact resolve eq797 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797
  have eq1184 : (M.op x y) = (M.op y (k y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq652 y
       have i₂ := eq682 y
       grind)
    | exact superpose eq682 eq652
    | exact resolve eq652 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq1193 : (M.op (σ x) (σ y)) = (M.op (k (σ y) (σ y)) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq640 sF3
       have i₂ := eq682 sF3
       grind)
    | exact superpose eq682 eq640
    | exact resolve eq640 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq1194 : (M.op (σ x) (σ y)) = (M.op (σ y) (k (σ y) (σ y))) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq631 sF3
       have i₂ := eq682 sF3
       grind)
    | exact superpose eq682 eq631
    | exact resolve eq631 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq1195 : (σ x) = (M.op (σ y) (k (σ y) (σ y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq648 eq1194
    | exact resolve eq1194 eq648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194
  have eq1196 : (σ x) = (M.op (k (σ y) (σ y)) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq648 eq1193
    | exact resolve eq1193 eq648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648 eq1193
  have eq1414 : (M.op x y) ≠ (M.op y y) ∨ (M.op (k y y) y) = (k y (k y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y (k y y)
       have i₂ := eq1184
       grind)
    | exact superpose eq1184 eq13
    | (have j0 := eq13 y (k y y)
       grind)
    | exact resolve eq13 eq1184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1417 : (M.op x y) = (k (k y y) y) ∨ y = (M.op (k y y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28 (k y y) y
       have i₂ := eq1184
       grind)
    | exact superpose eq1184 eq28
    | (have j0 := eq28 (k y y) y
       grind)
    | exact resolve eq28 eq1184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1425 : (M.op x y) = (k (k y y) y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1183 eq1417
    | exact resolve eq1417 eq1183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1417
  have eq1427 : (M.op x y) ≠ (k y y) ∨ (M.op (k y y) y) = (k y (k y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1414
       have i₂ := eq682 y
       grind)
    | exact superpose eq682 eq1414
    | exact resolve eq1414 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1414
  have eq1433 : (M.op x y) ≠ (k y y) ∨ (M.op x y) = (k y (k y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1183 eq1427
    | exact resolve eq1427 eq1183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1427
  have eq1437 : (M.op x y) = (k y (k y y)) ∨ (k y y) = (M.op y (k y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28 y (k y y)
       have i₂ := eq1183
       grind)
    | exact superpose eq1183 eq28
    | (have j0 := eq28 y (k y y)
       grind)
    | exact resolve eq28 eq1183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183
  have eq1440 : (M.op x y) = (k y (k y y)) ∨ (M.op x y) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1184 eq1437
    | exact resolve eq1437 eq1184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1437
  have eq1443 : (M.op x y) = (k y (k y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1440
       have r₂ := eq1433
       grind)
    | exact resolve eq1440 eq1433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1433 eq1440
  have eq1460 : (σ x) ≠ (M.op (σ y) (σ y)) ∨ (M.op (k (σ y) (σ y)) (σ y)) = (k (σ y) (k (σ y) (σ y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1195 eq13
    | (have j0 := eq13 (σ y) (k (σ y) (σ y))
       grind)
    | exact resolve eq13 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1463 : (σ x) = (k (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (k (σ y) (σ y)) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1195 eq28
    | (have j0 := eq28 (k (σ y) (σ y)) (σ y)
       grind)
    | exact resolve eq28 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1472 : (σ x) = (k (k (σ y) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1196 eq1463
    | exact resolve eq1463 eq1196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1463
  have eq1475 : (σ x) ≠ (k (σ y) (σ y)) ∨ (M.op (k (σ y) (σ y)) (σ y)) = (k (σ y) (k (σ y) (σ y))) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1460
       have i₂ := eq682 sF3
       grind)
    | exact superpose eq682 eq1460
    | exact resolve eq1460 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1460
  have eq1483 : (σ x) ≠ (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (k (σ y) (σ y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1196 eq1475
    | exact resolve eq1475 eq1196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475
  have eq1490 : (σ x) = (k (σ y) (k (σ y) (σ y))) ∨ (k (σ y) (σ y)) = (M.op (σ y) (k (σ y) (σ y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1196 eq28
    | (have j0 := eq28 (σ y) (k (σ y) (σ y))
       grind)
    | exact resolve eq28 eq1196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196
  have eq1494 : (σ x) = (k (σ y) (k (σ y) (σ y))) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1195 eq1490
    | exact resolve eq1490 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195 eq1490
  have eq1498 : (σ x) = (k (σ y) (k (σ y) (σ y))) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq1494
       have r₂ := eq1483
       grind)
    | exact resolve eq1494 eq1483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1483 eq1494
  have eq1504 : (τ (σ x)) = (k y (τ (k (σ y) (σ y)))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1498 eq108
    | exact resolve eq108 eq1498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1506 : (τ (σ x)) = (k y (k y y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq116 eq1504
    | exact resolve eq1504 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1504
  have eq1508 : x = (k y (k y y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq30 eq1506
    | exact resolve eq1506 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1506
  have eq1516 : (τ (σ (M.op x y))) = (k y y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1168 eq116
    | exact resolve eq116 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168
  have eq1533 : (M.op x y) = (k y y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq29 eq1516
    | exact resolve eq1516 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1516
  have eq1536 : (σ (M.op x y)) = (k (σ (k y y)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 (k y y)
       have i₂ := eq1425
       grind)
    | exact superpose eq1425 eq41
    | exact resolve eq41 eq1425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1425
  have eq1537 : (σ (M.op x y)) = (k (k (σ y) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1536
       have i₂ := eq41 y
       grind)
    | exact superpose eq41 eq1536
    | exact resolve eq1536 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1536
  have eq1538 : (σ (M.op x y)) = (k (k (σ y) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1537
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1537
    | exact resolve eq1537 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1537
  have eq1539 : (σ (M.op x y)) = (k (k (σ y) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1538
    | exact resolve eq1538 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538
  have eq1640 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq663 eq682
    | exact resolve eq682 eq663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq1647 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1051 eq1640
    | exact resolve eq1640 eq1051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1051 eq1640
  have eq1684 : (M.op x y) = (k y (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1443
       have i₂ := eq764
       grind)
    | exact superpose eq764 eq1443
    | exact resolve eq1443 eq764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq1691 : (M.op x y) = (k y (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by grind
  clear eq1684
  have eq1699 : (M.op x y) = (k y (k y (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | exact superpose eq831 eq1691
    | exact resolve eq1691 eq831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1691
  have eq1707 : (M.op x y) = (k y (k y (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) := by
    first
    | exact superpose eq831 eq1699
    | exact resolve eq1699 eq831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1699
  have eq1722 : (τ (σ x)) = (k (τ (k (σ y) (σ y))) y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1472 eq153
    | exact resolve eq153 eq1472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1472
  have eq1726 : (τ (σ x)) = (k (k y y) y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq116 eq1722
    | exact resolve eq1722 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq1722
  have eq1727 : x = (k (k y y) y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq30 eq1726
    | exact resolve eq1726 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1726
  have eq1901 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq182 X0 X1 X0
       have i₂ := eq682 X0
       grind)
    | exact superpose eq682 eq182
    | exact resolve eq182 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2185 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1647 eq153
    | exact resolve eq153 eq1647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq1647
  have eq2186 : (σ x) = (k (σ x) (σ x)) ∨ x = (k x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq30 eq2185
    | exact resolve eq2185 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2185
  have eq2220 : x = (k (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1727
       have i₂ := eq1533
       grind)
    | exact superpose eq1533 eq1727
    | exact resolve eq1727 eq1533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1727
  have eq2225 : x = (k (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq2220
  have eq2366 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (k x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2186 eq142
    | exact resolve eq142 eq2186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2186
  have eq2370 : x = (k x y) ∨ x = (k x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq30 eq2366
    | exact resolve eq2366 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2366
  have eq3267 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (M.op (σ y) X0)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq778 eq706
    | (have j0 := eq706 X0
       grind)
    | (have r₁ := eq706 X0
       have r₂ := eq778
       grind)
    | exact resolve eq706 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706 eq778
  have eq3268 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (M.op (σ y) X0)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq3267 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3267
  have eq3269 : ∀ X0 : G, (σ x) = (k (σ y) (M.op (σ y) X0)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq3268 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3268
  have eq3371 : ∀ X0 : G, (τ (σ x)) = (k y (τ (M.op (σ y) X0))) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq3269 eq108
    | exact resolve eq108 eq3269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq3269
  have eq3380 : ∀ X0 : G, x = (k y (τ (M.op (σ y) X0))) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq30 eq3371
    | exact resolve eq3371 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3371
  have eq3409 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op y X0)) (σ y)) ∨ y = (M.op (M.op y X0) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq41 (M.op y X0)
       have i₂ := eq800 X0
       grind)
    | exact superpose eq800 eq41
    | (have j1 := eq800 X0
       grind)
    | exact resolve eq41 eq800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800
  have eq3419 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op y X0)) (σ y)) ∨ y = (M.op (M.op y X0) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq3409
    | (have j0 := eq3409 X0
       grind)
    | exact resolve eq3409 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3409
  have eq3432 : ∀ X0 : G, y = (M.op y (k y y)) ∨ (σ (M.op x y)) = (k (σ (M.op y X0)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq3419 X0
       have i₂ := eq1178 y X0
       grind)
    | exact superpose eq1178 eq3419
    | (have j0 := eq3419 X0
       grind)
    | exact resolve eq3419 eq1178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3419
  have eq3443 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op y X0)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1184 eq3432
    | (have j0 := eq3432 X0
       grind)
    | exact resolve eq3432 eq1184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184 eq3432
  have eq3490 : ∀ X0 : G, (τ (σ (M.op x y))) = (k (M.op y X0) y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq3443 eq73
    | exact resolve eq73 eq3443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3443
  have eq3504 : ∀ X0 : G, (M.op x y) = (k (M.op y X0) y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq29 eq3490
    | exact resolve eq3490 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3490
  have eq3943 : x = (k y (τ (σ x))) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq624 eq3380
    | exact resolve eq3380 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624 eq3380
  have eq3957 : x = (k y (τ (σ x))) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq3943
  have eq3972 : x = (k y x) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq30 eq3957
    | exact resolve eq3957 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3957
  have eq3980 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq191 eq3972
    | exact resolve eq3972 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3972
  have eq3999 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3980 eq1498
    | exact resolve eq1498 eq3980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1498 eq3980
  have eq4014 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq3999
  have eq4036 : (τ (σ x)) = (k y (M.op x y)) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4014 eq117
    | exact resolve eq117 eq4014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq4014
  have eq4041 : x = (k y (M.op x y)) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq4036
    | exact resolve eq4036 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4036
  have eq4250 : ∀ X0 : G, (M.op x y) = (M.op y (M.op y X0)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq187 x y X0
       have i₂ := eq1045
       grind)
    | exact superpose eq1045 eq187
    | (have j0 := eq187 x y x
       grind)
    | exact resolve eq187 eq1045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045
  have eq4268 : ∀ X0 : G, (M.op x y) = (M.op y (M.op y X0)) ∨ y = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq2225 eq187
    | (have j0 := eq187 (M.op x y) y x
       grind)
    | exact resolve eq187 eq2225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4283 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq884 eq187
    | (have j0 := eq187 (σ x) (σ y) x
       grind)
    | exact resolve eq187 eq884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4425 : (M.op (σ x) (σ y)) = (M.op (σ y) (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4283 x
       have i₂ := eq1901 sF3 x
       grind)
    | exact superpose eq1901 eq4283
    | exact resolve eq4283 eq1901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4283
  have eq4436 : (M.op x y) = (M.op y (k y y)) ∨ y = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq4268 x
       have i₂ := eq1901 y x
       grind)
    | exact superpose eq1901 eq4268
    | exact resolve eq4268 eq1901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4268
  have eq4448 : (M.op x y) = (M.op y (k y y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq4250 x
       have i₂ := eq1901 y x
       grind)
    | exact superpose eq1901 eq4250
    | exact resolve eq4250 eq1901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4250
  have eq4497 : (M.op (σ x) (σ y)) = (M.op (σ y) (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq4425
    | exact resolve eq4425 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4425
  have eq4506 : (M.op x y) = (M.op y (k y y)) ∨ y = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq4436
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4436
    | exact resolve eq4436 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4436
  have eq4517 : (M.op x y) = (M.op y (k y y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq4448
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4448
    | exact resolve eq4448 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4448
  have eq4543 : (M.op (σ x) (σ y)) = (M.op (σ y) (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq4497
    | exact resolve eq4497 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4497
  have eq4552 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1533 eq4506
    | exact resolve eq4506 eq1533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1533 eq4506
  have eq4558 : (M.op x y) = (M.op y (k y y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq4517
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4517
    | exact resolve eq4517 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4517
  have eq4580 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq28 eq4552
    | (have j1 := eq28 (M.op x y) y
       grind)
    | exact resolve eq4552 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4552
  have eq4594 : x = (M.op x y) ∨ y = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2225 eq4580
    | exact resolve eq4580 eq2225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2225 eq4580
  have eq4597 : y = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq4594
       have r₂ := eq845
       grind)
    | exact resolve eq4594 eq845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845 eq4594
  have eq4621 : (M.op (σ x) (σ y)) = (k (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4543 eq28
    | (have j0 := eq28 (k (σ y) (σ y)) (σ y)
       grind)
    | exact resolve eq28 eq4543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4623 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ y) X0) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq4543 eq175
    | exact resolve eq175 eq4543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4625 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq4543 eq177
    | exact resolve eq177 eq4543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4638 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4625 x
       have i₂ := eq1178 sF3 x
       grind)
    | exact superpose eq1178 eq4625
    | exact resolve eq4625 eq1178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4625
  have eq4640 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (σ y) (k (σ y) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4623 x
       have i₂ := eq1178 sF3 x
       grind)
    | exact superpose eq1178 eq4623
    | exact resolve eq4623 eq1178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4623
  have eq4642 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1539 eq4621
    | exact resolve eq4621 eq1539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1539 eq4621
  have eq4651 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4543 eq4638
    | exact resolve eq4638 eq4543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4543 eq4638
  have eq4653 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4640
       have i₂ := eq1177 sF3 (k sF3 sF3)
       grind)
    | exact superpose eq1177 eq4640
    | exact resolve eq4640 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177 eq4640
  have eq4655 : (σ y) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq4642
       have r₂ := eq27
       grind)
    | exact resolve eq4642 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4642
  have eq4660 : (M.op (σ x) (σ y)) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4651 eq4653
    | exact resolve eq4653 eq4651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4651 eq4653
  have eq4663 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4655 eq4660
    | exact resolve eq4660 eq4655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4655 eq4660
  have eq4664 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4663
  have eq4666 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4664 eq215
    | exact resolve eq215 eq4664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4667 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4664 eq216
    | exact resolve eq216 eq4664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq4670 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4664 eq763
    | (have r₁ := eq763
       have r₂ := eq4664
       grind)
    | exact resolve eq763 eq4664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq4673 : (σ x) ≠ (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq4675 : (σ y) = (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4670
  have eq4676 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq884 eq4675
    | exact resolve eq4675 eq884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4675
  have eq4677 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq4666
    | exact resolve eq4666 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4666
  have eq4679 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4664 eq4677
    | exact resolve eq4677 eq4664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4677
  have eq4755 : (M.op (σ y) (σ x)) = (k (M.op (σ y) (σ x)) (σ x)) ∨ (σ x) = (M.op (M.op (σ y) (σ x)) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4667 eq28
    | (have j0 := eq28 (M.op (σ y) (σ x)) (σ x)
       grind)
    | exact resolve eq28 eq4667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq4667
  have eq4774 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (M.op (σ y) (σ x)) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4679 eq4755
    | exact resolve eq4755 eq4679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4755
  have eq4792 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4679 eq4774
    | exact resolve eq4774 eq4679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4774
  have eq5051 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4676 eq688
    | exact resolve eq688 eq4676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq5056 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq4676 eq187
    | (have j0 := eq187 (σ x) (σ x) x
       grind)
    | exact resolve eq187 eq4676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq4676
  have eq5058 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq5056 X0
       have j1 := eq193 (σ x)
       grind)
    | (have r₁ := eq5056 X0
       have r₂ := eq193 (σ x)
       grind)
    | exact resolve eq5056 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5056
  have eq5063 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq5051
       have r₂ := eq4664
       grind)
    | exact resolve eq5051 eq4664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5051
  have eq5064 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq181 eq5058
    | exact resolve eq5058 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq5058
  have eq5068 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq884 eq5063
    | exact resolve eq5063 eq884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884 eq5063
  have eq5069 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq215 eq5064
    | exact resolve eq5064 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq5064
  have eq5072 : (σ x) = (k (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5069
       have i₂ := eq682 sF2
       grind)
    | exact superpose eq682 eq5069
    | exact resolve eq5069 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5069
  have eq5073 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5068 eq5072
    | exact resolve eq5072 eq5068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5068 eq5072
  have eq5074 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4664 eq5073
    | exact resolve eq5073 eq4664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4664 eq5073
  have eq5075 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq5074
    | exact resolve eq5074 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5074
  have eq5076 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq5075
  have eq5081 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5076 eq142
    | exact resolve eq142 eq5076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5076
  have eq5088 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq5081
    | exact resolve eq5081 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5081
  have eq5092 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq831 eq5088
    | exact resolve eq5088 eq831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5088
  have eq5135 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4792 eq142
    | exact resolve eq142 eq4792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq4792
  have eq5142 : y = (k y x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq5135
    | exact resolve eq5135 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5135
  have eq5147 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (k y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq831 eq5142
    | exact resolve eq5142 eq831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831 eq5142
  have eq5618 : ∀ X0 : G, (M.op y (M.op x y)) = (k (M.op y X0) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq802 x
       have i₂ := eq189 y X0 x
       grind)
    | exact superpose eq189 eq802
    | (have j1 := eq189 y X0 x
       grind)
    | exact resolve eq802 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq802
  have eq5685 : ∀ X0 : G, y = (M.op y (k y y)) ∨ (M.op y (M.op x y)) = (k (M.op y X0) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq5618 X0
       have i₂ := eq1178 y X0
       grind)
    | exact superpose eq1178 eq5618
    | (have j0 := eq5618 X0
       grind)
    | exact resolve eq5618 eq1178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5618
  have eq5777 : ∀ X0 : G, y = (M.op y (k y y)) ∨ (M.op x y) = (k (M.op y X0) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq803 eq5685
    | exact resolve eq5685 eq803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803 eq5685
  have eq5835 : ∀ X0 : G, (M.op x y) = (k (M.op y X0) y) ∨ (M.op x y) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq3504 eq5777
    | (have j0 := eq5777 X0
       have j1 := eq3504 X0
       grind)
    | exact resolve eq5777 eq3504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3504 eq5777
  have eq6104 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5147 eq4679
    | exact resolve eq4679 eq5147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4679 eq5147
  have eq6124 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by grind
  clear eq6104
  have eq6137 : y = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq6124
       have r₂ := eq4673
       grind)
    | exact resolve eq6124 eq4673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4673 eq6124
  have eq6156 : (M.op x y) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6137 eq1707
    | exact resolve eq1707 eq6137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1707
  have eq6175 : (M.op x y) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq6156
  have eq6194 : (M.op x y) = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1443
       have i₂ := eq6175
       grind)
    | exact superpose eq6175 eq1443
    | exact resolve eq1443 eq6175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1443 eq6175
  have eq6207 : (M.op x y) = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq6194
  have eq6263 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6207 eq6137
    | exact resolve eq6137 eq6207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6137 eq6207
  have eq6271 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq6263
  have eq6284 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6271 eq27
    | exact resolve eq27 eq6271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6271
  have eq6447 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op y X0)) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq41 (M.op y X0)
       have i₂ := eq5835 X0
       grind)
    | exact superpose eq5835 eq41
    | exact resolve eq41 eq5835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq5835
  have eq6460 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op y X0)) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq6447
    | (have j0 := eq6447 X0
       grind)
    | exact resolve eq6447 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6447
  have eq6470 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op y X0)) (σ y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq982 eq6460
    | (have j0 := eq6460 X0
       grind)
    | exact resolve eq6460 eq982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq982 eq6460
  have eq6475 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op (M.op x y) X0)) (σ y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq5092 eq6470
    | exact resolve eq6470 eq5092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6470
  have eq6492 : ∀ X0 : G, (τ (σ (M.op x y))) = (k (M.op (M.op x y) X0) y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq6475 eq73
    | exact resolve eq73 eq6475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq6475
  have eq6507 : ∀ X0 : G, (M.op x y) = (k (M.op (M.op x y) X0) y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq29 eq6492
    | exact resolve eq6492 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq6492
  have eq6521 : ∀ X0 : G, (M.op x y) = (k (M.op (M.op x y) X0) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq5092 eq6507
    | exact resolve eq6507 eq5092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5092 eq6507
  have eq6532 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq805 eq6521
    | exact resolve eq6521 eq805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805 eq6521
  have eq6557 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6532
  have eq6576 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6557 eq42
    | exact resolve eq42 eq6557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq6557
  have eq6590 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq6576
    | exact resolve eq6576 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6576
  have eq9203 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq177 y X0 (k y y)
       have i₂ := eq4558
       grind)
    | exact superpose eq4558 eq177
    | exact resolve eq177 eq4558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9227 : (M.op (M.op x y) y) = (M.op y (k y y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq9203 x
       have i₂ := eq1178 y x
       grind)
    | exact superpose eq1178 eq9203
    | exact resolve eq9203 eq1178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9203
  have eq9248 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq4558 eq9227
    | exact resolve eq9227 eq4558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4558 eq9227
  have eq9267 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq9248 eq4597
    | exact resolve eq4597 eq9248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4597 eq9248
  have eq9292 : x = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq9267
  have eq9327 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq175 y x X0
       have i₂ := eq9292
       grind)
    | exact superpose eq9292 eq175
    | exact resolve eq175 eq9292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq9330 : ∀ X0 : G, (M.op x y) = (M.op (M.op y X0) y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq177 y X0 x
       have i₂ := eq9292
       grind)
    | exact superpose eq9292 eq177
    | exact resolve eq177 eq9292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq9335 : ∀ X0 : G, (M.op y x) = (M.op y (M.op y X0)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq182 y X0 x
       have i₂ := eq9292
       grind)
    | exact superpose eq9292 eq182
    | exact resolve eq182 eq9292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9348 : (M.op y x) = (M.op y (k y y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9335 x
       have i₂ := eq1901 y x
       grind)
    | exact superpose eq1901 eq9335
    | exact resolve eq9335 eq1901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9335
  have eq9353 : (M.op x y) = (M.op y (k y y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9330 x
       have i₂ := eq1178 y x
       grind)
    | exact superpose eq1178 eq9330
    | exact resolve eq9330 eq1178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9330
  have eq9356 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9327 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9327
    | (have j0 := eq9327 X0
       grind)
    | exact resolve eq9327 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9327
  have eq9364 : x = (M.op y (k y y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9292 eq9348
    | exact resolve eq9348 eq9292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9292 eq9348
  have eq9368 : (M.op x y) = (M.op y (k y y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9353
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9353
    | exact resolve eq9353 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9353
  have eq9371 : (M.op y (M.op x y)) = (M.op y (k y y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9356 x
       have i₂ := eq1178 y x
       grind)
    | exact superpose eq1178 eq9356
    | exact resolve eq9356 eq1178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178 eq9356
  have eq9377 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9368 eq9371
    | exact resolve eq9371 eq9368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9368 eq9371
  have eq9484 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq9377 eq182
    | exact resolve eq182 eq9377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq9493 : (M.op y (M.op x y)) = (M.op y (k y y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9484 x
       have i₂ := eq1901 y x
       grind)
    | exact superpose eq1901 eq9484
    | exact resolve eq9484 eq1901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1901 eq9484
  have eq9507 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9364 eq9493
    | exact resolve eq9493 eq9364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9364 eq9493
  have eq9519 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9377 eq9507
    | exact resolve eq9507 eq9377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9377 eq9507
  have eq9520 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq9519
  have eq9528 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9520 eq32
    | exact resolve eq32 eq9520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq9520
  have eq9667 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq9528
    | exact resolve eq9528 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq9528
  have eq9687 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq9667
       grind)
    | exact superpose eq9667 eq18
    | exact resolve eq18 eq9667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9691 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq191
       have i₂ := eq9667
       grind)
    | exact superpose eq9667 eq191
    | exact resolve eq191 eq9667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq9711 : x = (k (M.op x y) (k (M.op x y) (M.op x y))) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1508
       have i₂ := eq9667
       grind)
    | exact superpose eq9667 eq1508
    | exact resolve eq1508 eq9667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1508
  have eq9732 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq4041
       have i₂ := eq9667
       grind)
    | exact superpose eq9667 eq4041
    | exact resolve eq4041 eq9667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4041 eq9667
  have eq9740 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq9732
  have eq9752 : x = (k (M.op x y) x) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq9740 eq9711
    | exact resolve eq9711 eq9740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9711 eq9740
  have eq9758 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq194 eq9687
    | exact resolve eq9687 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194 eq9687
  have eq9760 : x = (M.op x y) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq9691 eq9752
    | exact resolve eq9752 eq9691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9691 eq9752
  have eq9761 : x = (M.op x y) ∨ x = (M.op (M.op x y) x) ∨ x = y := by grind
  clear eq9760
  have eq9762 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq9758 eq9761
    | exact resolve eq9761 eq9758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9758 eq9761
  have eq9763 : x = (M.op x y) ∨ x = y := by grind
  clear eq9762
  have eq9765 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq9763
       grind)
    | exact superpose eq9763 eq22
    | exact resolve eq22 eq9763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9787 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20 eq9765
    | exact resolve eq9765 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9765
  have eq9821 : (σ x) ≠ (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq9787 eq6284
    | (have r₁ := eq6284
       have r₂ := eq9787
       grind)
    | exact resolve eq6284 eq9787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6284 eq9787
  have eq9828 : y = (M.op x y) ∨ x = y := by grind
  clear eq9821
  have eq9911 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq9828
  have eq9915 : x = y := by
    first
    | (have r₁ := eq9911
       have r₂ := eq9763
       grind)
    | exact resolve eq9911 eq9763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9763 eq9911
  have eq9956 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq9915
       grind)
    | exact superpose eq9915 eq18
    | exact resolve eq18 eq9915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq9957 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq9915
       grind)
    | exact superpose eq9915 eq24
    | exact resolve eq24 eq9915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq9997 : x = (k x x) ∨ x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2370
       have i₂ := eq9915
       grind)
    | exact superpose eq9915 eq2370
    | exact resolve eq2370 eq9915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2370 eq9915
  have eq10025 : x = (k x x) ∨ x = (M.op x x) := by grind
  clear eq9997
  have eq10040 : x = (M.op x x) := by
    first
    | (have j1 := eq193 x
       grind)
    | (have r₁ := eq10025
       have r₂ := eq193 x
       grind)
    | exact resolve eq10025 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193 eq10025
  have eq10076 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq9957
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9957
    | exact resolve eq9957 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9957
  have eq10077 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq9956
       have i₂ := eq682 x
       grind)
    | exact superpose eq682 eq9956
    | exact resolve eq9956 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9956
  have eq10081 : x = (k x x) := by
    first
    | (have i₁ := eq10040
       have i₂ := eq682 x
       grind)
    | exact superpose eq682 eq10040
    | exact resolve eq10040 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10040
  have eq10111 : x = (M.op x y) := by
    first
    | (have i₁ := eq10081
       have i₂ := eq10077
       grind)
    | exact superpose eq10077 eq10081
    | exact resolve eq10081 eq10077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10077 eq10081
  have eq10125 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq10076 eq26
    | exact resolve eq26 eq10076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq10076
  have eq10267 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq10125
       have i₂ := eq682 sF2
       grind)
    | exact superpose eq682 eq10125
    | exact resolve eq10125 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682 eq10125
  have eq10444 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq10111
       grind)
    | exact superpose eq10111 eq22
    | exact resolve eq22 eq10111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq10111
  have eq10474 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq10444 eq20
    | exact resolve eq20 eq10444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq10444
  have eq10535 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10474 eq6590
    | exact resolve eq6590 eq10474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6590
  have eq10547 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10267 eq10535
    | exact resolve eq10535 eq10267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10267 eq10535
  have eq10548 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10547
  have eq10659 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq10548 eq27
    | exact resolve eq27 eq10548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq10548
  have eq10667 : False := by grind
  exact eq10667
