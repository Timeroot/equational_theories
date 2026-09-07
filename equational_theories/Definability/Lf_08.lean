import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(X,X) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_x_pxy_y_pxy_y_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8
    | exact resolve eq8 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (k X0 (τ X1))
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq8
    | exact resolve eq8 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq29 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq42 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X0 X2
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X1
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X0 X2) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq42 X0 X2 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq70 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq71 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq118 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq71 (σ X0) (σ X1)
       grind)
    | exact superpose eq71 eq13
    | (have j1 := eq71 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq71 (τ X0) X1
       grind)
    | exact superpose eq71 eq15
    | (have j1 := eq71 (τ X0) X1
       grind)
    | exact resolve eq15 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq71
  have eq1083 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq120 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq120
    | exact resolve eq120 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq1137 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1083 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1083
    | (have j0 := eq1083 X0 X1
       grind)
    | exact resolve eq1083 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083
  have eq1608 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq118 x y
       grind)
    | exact superpose eq118 eq14
    | (have j1 := eq118 x y
       grind)
    | exact resolve eq14 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1618 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq118 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq1635 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1618 (τ X0) (τ X1)
       have i₂ := eq29 X1 X0
       grind)
    | exact superpose eq29 eq1618
    | (have j0 := eq1618 (τ X0) (τ X1)
       grind)
    | exact resolve eq1618 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq1650 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1635 X0 X1
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq1635
    | (have j0 := eq1635 X0 X1
       grind)
    | exact resolve eq1635 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1635
  have eq1652 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1650 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq1650
    | (have j0 := eq1650 X0 X1
       grind)
    | exact resolve eq1650 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1650
  have eq1653 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1652 X0 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1652
    | (have j0 := eq1652 X0 X1
       grind)
    | exact resolve eq1652 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1652
  have eq1654 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1653 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1653
    | (have j0 := eq1653 X0 X1
       grind)
    | exact resolve eq1653 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1653
  have eq2374 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1608
       have i₂ := eq1137 x y
       grind)
    | exact superpose eq1137 eq1608
    | (have j1 := eq1137 (σ x) (σ y)
       grind)
    | (have r₁ := eq1608
       have r₂ := eq1137 x y
       grind)
    | exact resolve eq1608 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2375 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2374
  have eq2551 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2375
       grind)
    | exact superpose eq2375 eq14
    | exact resolve eq14 eq2375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2552 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq2375
       grind)
    | exact superpose eq2375 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq2375
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq2375
       grind)
    | exact resolve eq11 eq2375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2553 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2552
  have eq2554 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2553
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq2553
    | exact resolve eq2553 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2553
  have eq13835 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10 (σ x) X0
       have i₂ := eq2554
       grind)
    | exact superpose eq2554 eq10
    | (have j0 := eq10 (σ x) X0
       grind)
    | (have r₁ := eq10 (σ x) x
       have r₂ := eq2554
       grind)
    | exact resolve eq10 eq2554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2554
  have eq13838 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq13835 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13835
  have eq30832 : ∀ X0 : G, (k x (τ X0)) = (τ (M.op (σ x) X0)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq26 x X0
       have i₂ := eq13838 X0
       grind)
    | exact superpose eq13838 eq26
    | exact resolve eq26 eq13838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq13838
  have eq58146 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq30832 (σ y)
       have i₂ := eq2375
       grind)
    | exact superpose eq2375 eq30832
    | exact resolve eq30832 eq2375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2375 eq30832
  have eq58157 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by grind
  clear eq58146
  have eq58162 : y = (k x y) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq58157
       have i₂ := eq8 y
       grind)
    | exact superpose eq8 eq58157
    | exact resolve eq58157 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58157
  have eq58163 : (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq1654 x y
       grind)
    | (have r₁ := eq58162
       have r₂ := eq1654 x y
       grind)
    | exact resolve eq58162 eq1654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1654 eq58162
  have eq58332 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1137 x y
       have i₂ := eq58163
       grind)
    | exact superpose eq58163 eq1137
    | (have j0 := eq1137 x y
       grind)
    | exact resolve eq1137 eq58163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137 eq58163
  have eq58416 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq58332
  have eq58444 : y = (M.op x y) := by
    first
    | (have r₁ := eq58416
       have r₂ := eq2551
       grind)
    | exact resolve eq58416 eq2551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2551 eq58416
  have eq58617 : y ≠ y ∨ x = (M.op x x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq58444
       grind)
    | exact superpose eq58444 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq58444
       grind)
    | exact resolve eq11 eq58444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58618 : y = (k x y) ∨ x = (M.op x x) := by grind
  clear eq58617
  have eq59008 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1618 x y
       have i₂ := eq58618
       grind)
    | exact superpose eq58618 eq1618
    | (have j0 := eq1618 x y
       grind)
    | exact resolve eq1618 eq58618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1618 eq58618
  have eq59065 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq59008
  have eq60150 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq59065
       grind)
    | exact superpose eq59065 eq14
    | exact resolve eq14 eq59065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59065
  have eq60155 : (σ y) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq60150
       have i₂ := eq58444
       grind)
    | exact superpose eq58444 eq60150
    | exact resolve eq60150 eq58444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60150
  have eq60156 : x = (M.op x x) := by grind
  clear eq60155
  have eq60768 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq60156
       grind)
    | exact superpose eq60156 eq10
    | (have j0 := eq10 x X0
       grind)
    | (have r₁ := eq10 x x
       have r₂ := eq60156
       grind)
    | exact resolve eq10 eq60156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60156
  have eq60771 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq60768 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60768
  have eq61385 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1608
       have i₂ := eq60771 y
       grind)
    | exact superpose eq60771 eq1608
    | exact resolve eq1608 eq60771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1608 eq60771
  have eq61495 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq61385
  have eq62088 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq61495
       grind)
    | exact superpose eq61495 eq14
    | exact resolve eq14 eq61495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61495
  have eq62093 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq62088
       have i₂ := eq58444
       grind)
    | exact superpose eq58444 eq62088
    | exact resolve eq62088 eq58444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58444 eq62088
  have eq62094 : False := by grind
  exact eq62094

/-- `x □ y = if m(X,X) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_x_pyx_pyy_pyx_pyy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq29 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq29 X0
       have j1 := eq10 X0 X0
       grind)
    | (have r₁ := eq29 X0
       have r₂ := eq10 X0 x
       grind)
    | exact resolve eq29 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq32 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq30 (σ X0)
       grind)
    | exact superpose eq30 eq13
    | exact resolve eq13 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq32
    | exact resolve eq32 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq32
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X1 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq56 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq62 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq56 X0 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq56 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq106 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq62 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq156 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X0) X1
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq10
    | (have j0 := eq10 (σ X0) X1
       grind)
    | exact resolve eq10 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq164 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq156 X0 X1
       have j1 := eq106 (σ X0) X1
       grind)
    | (have r₁ := eq156 X0 (σ X0)
       have r₂ := eq106 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq156 X0 X1
       have r₂ := eq106 (σ X0) X1
       grind)
    | exact resolve eq156 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq156
  have eq168 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq164 X0 X1
       have j1 := eq158 X0 X1
       grind)
    | (have r₁ := eq164 X0 X1
       have r₂ := eq158 X0 X1
       grind)
    | exact resolve eq164 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158 eq164
  have eq204 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq168 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq168
    | exact resolve eq168 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq168 X1 (σ X0)
       grind)
    | exact superpose eq168 eq13
    | exact resolve eq13 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq754 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq209 x y
       grind)
    | exact superpose eq209 eq14
    | exact resolve eq14 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq778 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq754
       have i₂ := eq204 y x
       grind)
    | exact superpose eq204 eq754
    | exact resolve eq754 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq754
  have eq779 : False := by grind
  exact eq779

/-- `x □ y = if m(X,X) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_x_pyx_x_pyx_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8
    | exact resolve eq8 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq26 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (k X0 (τ X1))
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq8
    | exact resolve eq8 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq42 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op X2 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X0 X2
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X1
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X2 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq42 X0 X2 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq70 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq71 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq117 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq71 (σ X1) (σ X0)
       grind)
    | exact superpose eq71 eq13
    | (have j1 := eq71 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq71 X1 (τ X0)
       grind)
    | exact superpose eq71 eq16
    | (have j1 := eq71 X1 (τ X0)
       grind)
    | exact resolve eq16 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq71
  have eq905 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq121 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq121
    | exact resolve eq121 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq955 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq905 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq905
    | (have j0 := eq905 X0 X1
       grind)
    | exact resolve eq905 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq1628 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq117 x y
       grind)
    | exact superpose eq117 eq14
    | (have j1 := eq117 x y
       grind)
    | exact resolve eq14 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1638 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq117 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq1655 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1638 (τ X1) (τ X0)
       have i₂ := eq29 X1 X0
       grind)
    | exact superpose eq29 eq1638
    | (have j0 := eq1638 (τ X1) (τ X0)
       grind)
    | exact resolve eq1638 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq1670 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1655 X0 X1
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq1655
    | (have j0 := eq1655 X0 X1
       grind)
    | exact resolve eq1655 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1655
  have eq1672 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1670 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1670
    | (have j0 := eq1670 X0 X1
       grind)
    | exact resolve eq1670 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1670
  have eq1673 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1672 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1672
    | (have j0 := eq1672 X0 X1
       grind)
    | exact resolve eq1672 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1672
  have eq1674 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1673 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq1673
    | (have j0 := eq1673 X0 X1
       grind)
    | exact resolve eq1673 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1673
  have eq2524 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1628
       have i₂ := eq955 x y
       grind)
    | exact superpose eq955 eq1628
    | (have j1 := eq955 (σ x) (σ y)
       grind)
    | (have r₁ := eq1628
       have r₂ := eq955 x y
       grind)
    | exact resolve eq1628 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2525 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2524
  have eq2717 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2525
       grind)
    | exact superpose eq2525 eq14
    | exact resolve eq14 eq2525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2718 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ y) (σ x)
       have i₂ := eq2525
       grind)
    | exact superpose eq2525 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq2525
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq2525
       grind)
    | exact resolve eq11 eq2525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2719 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq2718
  have eq2720 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2719
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq2719
    | exact resolve eq2719 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2719
  have eq14800 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10 (σ y) X0
       have i₂ := eq2720
       grind)
    | exact superpose eq2720 eq10
    | (have j0 := eq10 (σ y) X0
       grind)
    | (have r₁ := eq10 (σ y) x
       have r₂ := eq2720
       grind)
    | exact resolve eq10 eq2720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2720
  have eq14803 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq14800 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14800
  have eq32387 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op X0 (σ y))) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq26 y X0
       have i₂ := eq14803 X0
       grind)
    | exact superpose eq14803 eq26
    | exact resolve eq26 eq14803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq14803
  have eq55539 : (τ (σ y)) = (k y (τ (σ x))) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq32387 (σ x)
       have i₂ := eq2525
       grind)
    | exact superpose eq2525 eq32387
    | exact resolve eq32387 eq2525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2525 eq32387
  have eq55549 : (τ (σ y)) = (k y (τ (σ x))) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by grind
  clear eq55539
  have eq55553 : (k y x) = (τ (σ y)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq55549
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq55549
    | exact resolve eq55549 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55549
  have eq55555 : y = (k y x) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq55553
       have i₂ := eq8 y
       grind)
    | exact superpose eq8 eq55553
    | exact resolve eq55553 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55553
  have eq55556 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq1674 y x
       grind)
    | (have r₁ := eq55555
       have r₂ := eq1674 y x
       grind)
    | exact resolve eq55555 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1674 eq55555
  have eq56109 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq955 x y
       have i₂ := eq55556
       grind)
    | exact superpose eq55556 eq955
    | (have j0 := eq955 x y
       grind)
    | exact resolve eq955 eq55556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955 eq55556
  have eq56195 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq56109
  have eq56223 : y = (M.op x y) := by
    first
    | (have r₁ := eq56195
       have r₂ := eq2717
       grind)
    | exact resolve eq56195 eq2717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2717 eq56195
  have eq56756 : y ≠ y ∨ y = (M.op y y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq56223
       grind)
    | exact superpose eq56223 eq11
    | (have j0 := eq11 y x
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq56223
       grind)
    | exact resolve eq11 eq56223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56757 : y = (k y x) ∨ y = (M.op y y) := by grind
  clear eq56756
  have eq57320 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1638 x y
       have i₂ := eq56757
       grind)
    | exact superpose eq56757 eq1638
    | (have j0 := eq1638 x y
       grind)
    | exact resolve eq1638 eq56757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1638 eq56757
  have eq57381 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq57320
  have eq58363 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq57381
       grind)
    | exact superpose eq57381 eq14
    | exact resolve eq14 eq57381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57381
  have eq58368 : (σ y) ≠ (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq58363
       have i₂ := eq56223
       grind)
    | exact superpose eq56223 eq58363
    | exact resolve eq58363 eq56223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58363
  have eq58369 : y = (M.op y y) := by grind
  clear eq58368
  have eq58934 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq58369
       grind)
    | exact superpose eq58369 eq10
    | (have j0 := eq10 y X0
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq58369
       grind)
    | exact resolve eq10 eq58369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58369
  have eq58937 : ∀ X0 : G, (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq58934 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58934
  have eq59500 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1628
       have i₂ := eq58937 x
       grind)
    | exact superpose eq58937 eq1628
    | exact resolve eq1628 eq58937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1628 eq58937
  have eq59617 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq59500
  have eq60259 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq59617
       grind)
    | exact superpose eq59617 eq14
    | exact resolve eq14 eq59617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59617
  have eq60264 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq60259
       have i₂ := eq56223
       grind)
    | exact superpose eq56223 eq60259
    | exact resolve eq60259 eq56223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56223 eq60259
  have eq60265 : False := by grind
  exact eq60265

/-- `x □ y = if m(X,X) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_x_pyx_y_pyx_y_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8
    | exact resolve eq8 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (k X0 (τ X1))
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq8
    | exact resolve eq8 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq29 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq42 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X2) = (M.op X2 X0) ∨ (M.op X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X0 X2
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X1
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X2 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq42 X0 X2 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq70 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq71 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq117 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq71 (σ X1) (σ X0)
       grind)
    | exact superpose eq71 eq13
    | (have j1 := eq71 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq71 (τ X1) X0
       grind)
    | exact superpose eq71 eq15
    | (have j1 := eq71 (τ X1) X0
       grind)
    | exact resolve eq15 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq71
  have eq1186 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq119 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq119
    | exact resolve eq119 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq1241 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1186 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1186
    | (have j0 := eq1186 X0 X1
       grind)
    | exact resolve eq1186 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186
  have eq1597 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq117 x y
       grind)
    | exact superpose eq117 eq14
    | (have j1 := eq117 x y
       grind)
    | exact resolve eq14 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1607 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq117 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq1702 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1607 (τ X1) (τ X0)
       have i₂ := eq29 X1 X0
       grind)
    | exact superpose eq29 eq1607
    | (have j0 := eq1607 (τ X1) (τ X0)
       grind)
    | exact resolve eq1607 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq1718 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1702 X0 X1
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq1702
    | (have j0 := eq1702 X0 X1
       grind)
    | exact resolve eq1702 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1702
  have eq1720 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1718 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq1718
    | (have j0 := eq1718 X0 X1
       grind)
    | exact resolve eq1718 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1718
  have eq1721 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1720 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1720
    | (have j0 := eq1720 X0 X1
       grind)
    | exact resolve eq1720 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1720
  have eq1722 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1721 X0 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1721
    | (have j0 := eq1721 X0 X1
       grind)
    | exact resolve eq1721 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1721
  have eq2528 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1597
       have i₂ := eq1241 y x
       grind)
    | exact superpose eq1241 eq1597
    | (have j1 := eq1241 (σ y) (σ x)
       grind)
    | (have r₁ := eq1597
       have r₂ := eq1241 y x
       grind)
    | exact resolve eq1597 eq1241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2529 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2528
  have eq2717 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2529
       grind)
    | exact superpose eq2529 eq14
    | exact resolve eq14 eq2529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2718 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ y) (σ x)
       have i₂ := eq2529
       grind)
    | exact superpose eq2529 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq2529
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq2529
       grind)
    | exact resolve eq11 eq2529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2719 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq2718
  have eq2720 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2719
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq2719
    | exact resolve eq2719 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2719
  have eq14618 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10 (σ y) X0
       have i₂ := eq2720
       grind)
    | exact superpose eq2720 eq10
    | (have j0 := eq10 (σ y) X0
       grind)
    | (have r₁ := eq10 (σ y) x
       have r₂ := eq2720
       grind)
    | exact resolve eq10 eq2720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2720
  have eq14621 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq14618 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14618
  have eq32088 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op X0 (σ y))) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq26 y X0
       have i₂ := eq14621 X0
       grind)
    | exact superpose eq14621 eq26
    | exact resolve eq26 eq14621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq14621
  have eq54764 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq32088 (σ x)
       have i₂ := eq2529
       grind)
    | exact superpose eq2529 eq32088
    | exact resolve eq32088 eq2529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2529 eq32088
  have eq54774 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by grind
  clear eq54764
  have eq54778 : x = (k y x) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq54774
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq54774
    | exact resolve eq54774 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54774
  have eq54780 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq1722 y x
       grind)
    | (have r₁ := eq54778
       have r₂ := eq1722 y x
       grind)
    | exact resolve eq54778 eq1722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1722 eq54778
  have eq55321 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1241 y x
       have i₂ := eq54780
       grind)
    | exact superpose eq54780 eq1241
    | (have j0 := eq1241 y x
       grind)
    | exact resolve eq1241 eq54780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241 eq54780
  have eq55405 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq55321
  have eq55433 : x = (M.op x y) := by
    first
    | (have r₁ := eq55405
       have r₂ := eq2717
       grind)
    | exact resolve eq55405 eq2717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2717 eq55405
  have eq55982 : x ≠ x ∨ y = (M.op y y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq55433
       grind)
    | exact superpose eq55433 eq11
    | (have j0 := eq11 y x
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq55433
       grind)
    | exact resolve eq11 eq55433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55983 : x = (k y x) ∨ y = (M.op y y) := by grind
  clear eq55982
  have eq56618 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1607 x y
       have i₂ := eq55983
       grind)
    | exact superpose eq55983 eq1607
    | (have j0 := eq1607 x y
       grind)
    | exact resolve eq1607 eq55983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1607 eq55983
  have eq56675 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq56618
  have eq57797 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq56675
       grind)
    | exact superpose eq56675 eq14
    | exact resolve eq14 eq56675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56675
  have eq57802 : (σ x) ≠ (σ x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq57797
       have i₂ := eq55433
       grind)
    | exact superpose eq55433 eq57797
    | exact resolve eq57797 eq55433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57797
  have eq57803 : y = (M.op y y) := by grind
  clear eq57802
  have eq58327 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq57803
       grind)
    | exact superpose eq57803 eq10
    | (have j0 := eq10 y X0
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq57803
       grind)
    | exact resolve eq10 eq57803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57803
  have eq58330 : ∀ X0 : G, (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq58327 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58327
  have eq58947 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1597
       have i₂ := eq58330 x
       grind)
    | exact superpose eq58330 eq1597
    | exact resolve eq1597 eq58330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1597 eq58330
  have eq59055 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq58947
  have eq59710 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq59055
       grind)
    | exact superpose eq59055 eq14
    | exact resolve eq14 eq59055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59055
  have eq59715 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq59710
       have i₂ := eq55433
       grind)
    | exact superpose eq55433 eq59710
    | exact resolve eq59710 eq55433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55433 eq59710
  have eq59716 : False := by grind
  exact eq59716

/-- `x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_x_pyy_y_pxy_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8
    | exact resolve eq8 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X0 X2
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X1
       have j1 := eq12 X2 X2
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq12 X2 X0
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X1 X0
       have j1 := eq12 X1 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X2 X0
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X1
       have j1 := eq12 X2 X2
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op (τ X1) (τ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 (τ X1) (τ X1)
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq46 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq41 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq47 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq40 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq48 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq39 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq50 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq47 X0 X2 X2
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq47 X0 X0 X2
       have r₂ := eq10 X0 X1
       grind)
    | (have r₁ := eq47 X0 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq47 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq76 : ∀ X0 X1 X2 X3 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X2 X3) = (M.op X2 X3) ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq46 X2 X3 X0
       grind)
    | exact superpose eq46 eq11
    | (have j0 := eq11 X1 X0
       have j1 := eq46 X1 X0 X1
       grind)
    | (have r₁ := eq11 X0 X2
       have r₂ := eq46 X0 X1 X2
       grind)
    | exact resolve eq11 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq46 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq85 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq84 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq88 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X2 X3) = (M.op X2 X3) ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq76 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq89 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq85 X0
       have j1 := eq10 X0 X0
       grind)
    | (have r₁ := eq85 X0
       have r₂ := eq10 X0 x
       grind)
    | exact resolve eq85 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq91 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X2 X3) = (M.op X2 X3) ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq88 X0 X1 X2 X3
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq88 X0 X0 X2 X3
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq88 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq93 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq89 (σ X0)
       grind)
    | exact superpose eq89 eq13
    | exact resolve eq13 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq16 X0 (τ X0)
       have i₂ := eq89 (τ X0)
       grind)
    | exact superpose eq89 eq16
    | exact resolve eq16 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq97 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq97
    | exact resolve eq97 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq102 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq93 X0
       have i₂ := eq89 X0
       grind)
    | exact superpose eq89 eq93
    | exact resolve eq93 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq104 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq98 X0
       have i₂ := eq89 X0
       grind)
    | exact superpose eq89 eq98
    | exact resolve eq98 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq98
  have eq126 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) X2) = (M.op (σ X1) X2) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq48 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq48 eq13
    | (have j1 := eq48 (σ X1) X2 (σ X0)
       grind)
    | exact resolve eq13 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq137 : ∀ X0 X1 X2 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) X2) = (M.op (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq126 X0 X1 X2
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq126
    | (have j0 := eq126 X0 X1 X2
       grind)
    | exact resolve eq126 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq195 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq50 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq198 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq195 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq195 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq195 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq214 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X0) X1
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq10
    | (have j0 := eq10 (σ X0) X1
       grind)
    | exact resolve eq10 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (σ X0)
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq11
    | (have j0 := eq11 X1 (σ X0)
       grind)
    | exact resolve eq11 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq12
    | (have j0 := eq12 X1 X1
       grind)
    | exact resolve eq12 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq215 X0 X1
       have j1 := eq10 X1 (σ X0)
       grind)
    | (have r₁ := eq215 X0 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq215 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq1345 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq91 X1 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq1352 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1345 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1345
  have eq1377 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1352 X1 X0
       have i₂ := eq1352 X0 X1
       grind)
    | exact superpose eq1352 eq1352
    | (have j0 := eq1352 X1 X0
       have j1 := eq1352 X1 X0
       grind)
    | exact resolve eq1352 eq1352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1438 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (k (τ X0) (τ X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq1352 (τ X0) (τ X1)
       grind)
    | exact superpose eq1352 eq29
    | (have j1 := eq1352 (τ X0) (τ X1)
       grind)
    | exact resolve eq29 eq1352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1352
  have eq1449 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1438 X0 X1
       have i₂ := eq29 X1 X0
       grind)
    | exact superpose eq29 eq1438
    | (have j0 := eq1438 X0 X1
       grind)
    | exact resolve eq1438 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1438
  have eq1467 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1377 X0 X1
       have j1 := eq198 X1 X0
       grind)
    | (have r₁ := eq1377 X0 X1
       have r₂ := eq198 X0 X1
       grind)
    | (have r₁ := eq1377 X1 X0
       have r₂ := eq198 X0 X1
       grind)
    | exact resolve eq1377 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1377
  have eq2141 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (M.op X0 X0) ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq221 (τ X0) X1
       have i₂ := eq104 X0
       grind)
    | exact superpose eq104 eq221
    | (have j0 := eq221 (τ X0) X1
       grind)
    | exact resolve eq221 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq2154 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2141 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2141
    | (have j0 := eq2141 X0 X1
       grind)
    | exact resolve eq2141 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2141
  have eq2159 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2154 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2154
    | (have j0 := eq2154 X0 X1
       grind)
    | exact resolve eq2154 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2154
  have eq2855 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq43
    | (have j0 := eq43 X0 X1
       grind)
    | exact resolve eq43 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq3020 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2855 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2855
    | (have j0 := eq2855 X0 X0
       grind)
    | exact resolve eq2855 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2855
  have eq3115 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ (k X0 X2)) = (σ (M.op X2 X0)) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq214 X0 X1
       have i₂ := eq3020 X0 X2
       grind)
    | exact superpose eq3020 eq214
    | (have j0 := eq214 X0 X1
       have j1 := eq3020 X0 X2
       grind)
    | exact resolve eq214 eq3020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3145 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (σ (k X1 (τ X0))) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq104 X0
       have i₂ := eq3020 X1 (τ X0)
       grind)
    | exact superpose eq3020 eq104
    | (have j1 := eq3020 X1 (τ X0)
       grind)
    | exact resolve eq104 eq3020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq3020
  have eq3167 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ (k X0 X2)) = (σ (M.op X2 X0)) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq3115 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3115
  have eq3174 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X1 (τ X0))) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3145 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq3145
    | (have j0 := eq3145 X0 X1
       grind)
    | exact resolve eq3145 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3145
  have eq3224 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3174 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq3174
    | (have j0 := eq3174 X0 X0
       grind)
    | exact resolve eq3174 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq3174
  have eq11933 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) X2) = (M.op (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X0 X0)
       have i₂ := eq137 X0 X1 X2
       grind)
    | exact superpose eq137 eq8
    | (have j1 := eq137 X0 X1 X2
       grind)
    | exact resolve eq8 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq12138 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) X2) = (M.op (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11933 X0 X1 X2
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq11933
    | (have j0 := eq11933 X0 X1 X2
       grind)
    | exact resolve eq11933 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11933
  have eq32055 : ∀ X0 X1 : G, (τ (k X1 X0)) ≠ (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1449 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1449
  have eq32867 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (k (σ X1) (σ X0))) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq32055 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq32055
    | exact resolve eq32055 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32055
  have eq32883 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (k (τ (σ X1)) X0) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq32867 X0 X1
       have i₂ := eq20 (σ X1) X0
       grind)
    | exact superpose eq20 eq32867
    | (have j0 := eq32867 X0 X1
       grind)
    | exact resolve eq32867 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq32867
  have eq32890 : ∀ X0 X1 : G, (k X1 X0) ≠ (τ (σ (k X0 X1))) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq32883 X0 X1
       have i₂ := eq8 X1
       grind)
    | exact superpose eq8 eq32883
    | (have j0 := eq32883 X0 X1
       grind)
    | exact resolve eq32883 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32883
  have eq32895 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq32890 X0 X1
       have i₂ := eq8 (k X0 X1)
       grind)
    | exact superpose eq8 eq32890
    | (have j0 := eq32890 X0 X1
       grind)
    | (have r₁ := eq32890 X1 X1
       have r₂ := eq8 (k X1 X1)
       grind)
    | exact resolve eq32890 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32890
  have eq32899 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) X1) ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq32895 X0 X1
       have i₂ := eq8 X1
       grind)
    | exact superpose eq8 eq32895
    | (have j0 := eq32895 X0 X1
       grind)
    | exact resolve eq32895 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32895
  have eq32901 : ∀ X0 X1 : G, (M.op X0 X1) = (τ (σ (k X0 X1))) ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq32899 X0 X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq32899
    | (have j0 := eq32899 X0 X1
       grind)
    | exact resolve eq32899 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32899
  have eq32903 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq32901 X0 X1
       have i₂ := eq8 (k X0 X1)
       grind)
    | exact superpose eq8 eq32901
    | (have j0 := eq32901 X0 X1
       grind)
    | exact resolve eq32901 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32901
  have eq32931 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq32903 X1 X0
       have i₂ := eq1467 X0 X1
       grind)
    | exact superpose eq1467 eq32903
    | (have j0 := eq32903 X1 X0
       have j1 := eq1467 X0 X1
       grind)
    | exact resolve eq32903 eq1467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1467 eq32903
  have eq33010 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32931 X0 X1
       have j1 := eq198 X1 X0
       grind)
    | (have r₁ := eq32931 X0 X1
       have r₂ := eq198 X0 X1
       grind)
    | (have r₁ := eq32931 X1 X0
       have r₂ := eq198 X0 X1
       grind)
    | exact resolve eq32931 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq32931
  have eq34285 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k (σ X1) (σ X0)) = (σ (M.op (τ (σ X0)) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq102 X0
       have i₂ := eq3224 (σ X0) X1
       grind)
    | exact superpose eq3224 eq102
    | (have j1 := eq3224 (σ X0) X1
       grind)
    | exact resolve eq102 eq3224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3224
  have eq34332 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34285 X0 X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq34285
    | (have j0 := eq34285 X0 X1
       grind)
    | exact resolve eq34285 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34285
  have eq34349 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34332 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq34332
    | (have j0 := eq34332 X0 X1
       grind)
    | exact resolve eq34332 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34332
  have eq35313 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x x) ∨ (M.op (σ y) X0) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq12138 x y X0
       grind)
    | exact superpose eq12138 eq14
    | (have j1 := eq12138 x y X0
       grind)
    | exact resolve eq14 eq12138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12138
  have eq35336 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq35313 X0
       have j1 := eq3167 y X0 x
       grind)
    | (have r₁ := eq35313 X0
       have r₂ := eq3167 y x x
       grind)
    | exact resolve eq35313 eq3167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3167 eq35313
  have eq35420 : ∀ X0 : G, (M.op (σ y) X0) ≠ (M.op (σ y) X0) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq33010 (σ y) X0
       have i₂ := eq35336 X0
       grind)
    | exact superpose eq35336 eq33010
    | (have j0 := eq33010 (σ y) X0
       grind)
    | (have r₁ := eq33010 (σ y) X0
       have r₂ := eq35336 X0
       grind)
    | exact resolve eq33010 eq35336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33010 eq35336
  have eq35448 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq35420 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35420
  have eq35801 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq35448 (σ X0)
       grind)
    | exact superpose eq35448 eq13
    | exact resolve eq13 eq35448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35448
  have eq37785 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq35801 x
       grind)
    | exact superpose eq35801 eq14
    | exact resolve eq14 eq35801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35801
  have eq162520 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X0 X0)
       have i₂ := eq216 X0 X1
       grind)
    | exact superpose eq216 eq8
    | (have j1 := eq216 X0 X1
       grind)
    | exact resolve eq8 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq162529 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq162520 X0 X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq162520
    | (have j0 := eq162520 X0 X1
       grind)
    | exact resolve eq162520 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162520
  have eq162564 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq162529 X1 (σ X0)
       grind)
    | exact superpose eq162529 eq13
    | (have j1 := eq162529 X1 X1
       grind)
    | exact resolve eq13 eq162529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162529
  have eq162578 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq162564 X0 X1
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq162564
    | (have j0 := eq162564 X0 X1
       grind)
    | exact resolve eq162564 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq162564
  have eq210861 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq162578 x y
       grind)
    | exact superpose eq162578 eq14
    | (have j1 := eq162578 x y
       grind)
    | exact resolve eq14 eq162578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162578
  have eq210862 : (σ x) = (σ (M.op x x)) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq34349 x y
       grind)
    | (have r₁ := eq210861
       have r₂ := eq34349 x y
       grind)
    | exact resolve eq210861 eq34349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34349 eq210861
  have eq210876 : (M.op x x) = (τ (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq8 (M.op x x)
       have i₂ := eq210862
       grind)
    | exact superpose eq210862 eq8
    | exact resolve eq8 eq210862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210862
  have eq210947 : y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq210876
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq210876
    | exact resolve eq210876 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210876
  have eq210958 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq2159 y X0
       have i₂ := eq210947
       grind)
    | exact superpose eq210947 eq2159
    | (have j0 := eq2159 y X0
       grind)
    | (have r₁ := eq2159 y x
       have r₂ := eq210947
       grind)
    | (have r₁ := eq2159 x x
       have r₂ := eq210947
       grind)
    | exact resolve eq2159 eq210947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2159 eq210947
  have eq210971 : ∀ X0 : G, (M.op X0 y) = (k X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq210958 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210958
  have eq211057 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq37785
       have i₂ := eq210971 x
       grind)
    | exact superpose eq210971 eq37785
    | exact resolve eq37785 eq210971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37785 eq210971
  have eq211065 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) := by grind
  clear eq211057
  have eq211066 : x = (M.op x x) := by grind
  clear eq211065
  have eq211093 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq211066
       grind)
    | exact superpose eq211066 eq10
    | (have j0 := eq10 x X0
       grind)
    | (have r₁ := eq10 x x
       have r₂ := eq211066
       grind)
    | exact resolve eq10 eq211066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211095 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq214 x X0
       have i₂ := eq211066
       grind)
    | exact superpose eq211066 eq214
    | (have j0 := eq214 x X0
       grind)
    | exact resolve eq214 eq211066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq211066
  have eq211132 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq211095 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211095
  have eq211134 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq211093 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211093
  have eq215779 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq211132 (σ X0)
       grind)
    | exact superpose eq211132 eq13
    | exact resolve eq13 eq211132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211132
  have eq216027 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq215779 X0
       have i₂ := eq211134 X0
       grind)
    | exact superpose eq211134 eq215779
    | exact resolve eq215779 eq211134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211134 eq215779
  have eq220102 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq216027 y
       grind)
    | exact superpose eq216027 eq14
    | (have r₁ := eq14
       have r₂ := eq216027 y
       grind)
    | exact resolve eq14 eq216027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216027
  have eq220293 : False := by grind
  exact eq220293

/-- `x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_x_pyy_y_pyx_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq8
    | exact resolve eq8 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X0 X2
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X1
       have j1 := eq12 X2 X2
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq12 X2 X0
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X1 X0
       have j1 := eq12 X1 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X2 X0
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X1
       have j1 := eq12 X2 X2
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 (τ X0) (τ X0)
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq46 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq41 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq47 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq40 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq48 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq39 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq50 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq47 X0 X2 X2
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq47 X0 X0 X2
       have r₂ := eq10 X0 X1
       grind)
    | (have r₁ := eq47 X0 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq47 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq76 : ∀ X0 X1 X2 X3 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (k X2 X3) = (M.op X3 X2) ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq46 X2 X3 X0
       grind)
    | exact superpose eq46 eq11
    | (have j0 := eq11 X1 X0
       have j1 := eq46 X1 X0 X1
       grind)
    | (have r₁ := eq11 X0 X2
       have r₂ := eq46 X0 X1 X2
       grind)
    | exact resolve eq11 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq46 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq85 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq84 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq88 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (k X2 X3) = (M.op X3 X2) ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq76 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq89 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq85 X0
       have j1 := eq10 X0 X0
       grind)
    | (have r₁ := eq85 X0
       have r₂ := eq10 X0 x
       grind)
    | exact resolve eq85 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq91 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X2 X3) = (M.op X3 X2) ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq88 X0 X1 X2 X3
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq88 X0 X0 X2 X3
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq88 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq93 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq89 (σ X0)
       grind)
    | exact superpose eq89 eq13
    | exact resolve eq13 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq16 X0 (τ X0)
       have i₂ := eq89 (τ X0)
       grind)
    | exact superpose eq89 eq16
    | exact resolve eq16 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq97 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq97
    | exact resolve eq97 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq102 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq93 X0
       have i₂ := eq89 X0
       grind)
    | exact superpose eq89 eq93
    | exact resolve eq93 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq104 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq98 X0
       have i₂ := eq89 X0
       grind)
    | exact superpose eq89 eq98
    | exact resolve eq98 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq98
  have eq126 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 (σ X0)) = (k (σ X0) X2) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq48 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq48 eq13
    | (have j1 := eq48 (σ X0) X2 (σ X1)
       grind)
    | exact resolve eq13 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq137 : ∀ X0 X1 X2 : G, (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 (σ X0)) = (k (σ X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq126 X0 X1 X2
       have i₂ := eq102 X1
       grind)
    | exact superpose eq102 eq126
    | (have j0 := eq126 X0 X1 X2
       grind)
    | exact resolve eq126 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq186 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X2 (σ X1)) = (M.op (σ X1) X2) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq50 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq50 eq13
    | (have j1 := eq50 (σ X1) X2 (σ X0)
       grind)
    | exact resolve eq13 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq50 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq198 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq195 X0 X1
       have j1 := eq10 X0 X1
       grind)
    | (have r₁ := eq195 X0 X1
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq195 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq202 : ∀ X0 X1 X2 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X2 (σ X1)) = (M.op (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq186 X0 X1 X2
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq186
    | (have j0 := eq186 X0 X1 X2
       grind)
    | exact resolve eq186 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq214 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X0) X1
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq10
    | (have j0 := eq10 (σ X0) X1
       grind)
    | exact resolve eq10 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (σ X0)
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq11
    | (have j0 := eq11 X1 (σ X0)
       grind)
    | exact resolve eq11 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq12
    | (have j0 := eq12 X1 X1
       grind)
    | exact resolve eq12 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq215 X0 X1
       have j1 := eq10 X1 (σ X0)
       grind)
    | (have r₁ := eq215 X0 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq215 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq1346 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq91 X1 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq1353 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1346 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1346
  have eq1378 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1353 X0 X1
       have i₂ := eq1353 X1 X0
       grind)
    | exact superpose eq1353 eq1353
    | (have j0 := eq1353 X0 X1
       have j1 := eq1353 X0 X1
       grind)
    | exact resolve eq1353 eq1353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1430 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq1353 (σ X1) (σ X0)
       grind)
    | exact superpose eq1353 eq13
    | (have j1 := eq1353 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq1353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1439 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 X0
       have i₂ := eq1353 (τ X1) (τ X0)
       grind)
    | exact superpose eq1353 eq29
    | (have j1 := eq1353 (τ X1) (τ X0)
       grind)
    | exact resolve eq29 eq1353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1353
  have eq1450 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1439 X0 X1
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq1439
    | (have j0 := eq1439 X0 X1
       grind)
    | exact resolve eq1439 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1439
  have eq1453 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1430 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1430
    | (have j0 := eq1430 X0 X1
       grind)
    | exact resolve eq1430 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1430
  have eq1469 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1378 X0 X1
       have j1 := eq198 X0 X1
       grind)
    | (have r₁ := eq1378 X0 X1
       have r₂ := eq198 X0 X1
       grind)
    | (have r₁ := eq1378 X1 X0
       have r₂ := eq198 X0 X1
       grind)
    | exact resolve eq1378 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1378
  have eq1709 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1469 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2148 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (M.op X0 X0) ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq221 (τ X0) X1
       have i₂ := eq104 X0
       grind)
    | exact superpose eq104 eq221
    | (have j0 := eq221 (τ X0) X1
       grind)
    | exact resolve eq221 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2161 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2148 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2148
    | (have j0 := eq2148 X0 X1
       grind)
    | exact resolve eq2148 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2148
  have eq2166 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2161 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2161
    | (have j0 := eq2161 X0 X1
       grind)
    | exact resolve eq2161 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2161
  have eq2860 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq43
    | (have j0 := eq43 X0 X0
       grind)
    | exact resolve eq43 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq3025 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2860 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2860
    | (have j0 := eq2860 X0 X0
       grind)
    | exact resolve eq2860 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2860
  have eq3120 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ (k X0 X2)) = (σ (M.op X0 X2)) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq214 X0 X1
       have i₂ := eq3025 X0 X2
       grind)
    | exact superpose eq3025 eq214
    | (have j0 := eq214 X0 X1
       have j1 := eq3025 X0 X2
       grind)
    | exact resolve eq214 eq3025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3139 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq221 X0 X1
       have i₂ := eq3025 X2 X0
       grind)
    | exact superpose eq3025 eq221
    | (have j0 := eq221 X0 X1
       have j1 := eq3025 X2 X0
       grind)
    | exact resolve eq221 eq3025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq3150 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (σ (k X1 (τ X0))) = (σ (M.op X1 (τ X0))) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq104 X0
       have i₂ := eq3025 X1 (τ X0)
       grind)
    | exact superpose eq3025 eq104
    | (have j1 := eq3025 X1 (τ X0)
       grind)
    | exact resolve eq104 eq3025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq3025
  have eq3160 : ∀ X0 X1 X2 : G, (M.op (σ X0) X1) = (k X1 (σ X0)) ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq3139 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3139
  have eq3172 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ (k X0 X2)) = (σ (M.op X0 X2)) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq3120 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3120
  have eq3179 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X1 (τ X0))) = (σ (M.op X1 (τ X0))) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3150 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq3150
    | (have j0 := eq3150 X0 X1
       grind)
    | exact resolve eq3150 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3150
  have eq3229 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op X1 (τ X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3179 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq3179
    | (have j0 := eq3179 X0 X0
       grind)
    | exact resolve eq3179 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq3179
  have eq11945 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k (σ X1) X2) = (M.op X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X0 X0)
       have i₂ := eq137 X1 X0 X2
       grind)
    | exact superpose eq137 eq8
    | (have j1 := eq137 X1 X0 X2
       grind)
    | exact resolve eq8 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq12150 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k (σ X1) X2) = (M.op X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11945 X0 X1 X2
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq11945
    | (have j0 := eq11945 X0 X1 X2
       grind)
    | exact resolve eq11945 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11945
  have eq12683 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X2 (σ X1)) = (M.op (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X0 X0)
       have i₂ := eq202 X0 X1 X2
       grind)
    | exact superpose eq202 eq8
    | (have j1 := eq202 X0 X1 X2
       grind)
    | exact resolve eq8 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq12896 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X2 (σ X1)) = (M.op (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12683 X0 X1 X2
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq12683
    | (have j0 := eq12683 X0 X1 X2
       grind)
    | exact resolve eq12683 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12683
  have eq30026 : ∀ X0 X1 : G, (τ (k X1 X0)) ≠ (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1450 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30027 : ∀ X0 X1 : G, (τ (k X1 X0)) ≠ (τ (k X0 X1)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1450 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1450
  have eq30149 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (k (σ X1) (σ X0))) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq30026 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq30026
    | exact resolve eq30026 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30026
  have eq30164 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (k (τ (σ X1)) X0) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq30149 X0 X1
       have i₂ := eq20 (σ X1) X0
       grind)
    | exact superpose eq20 eq30149
    | (have j0 := eq30149 X0 X1
       grind)
    | exact resolve eq30149 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30149
  have eq30171 : ∀ X0 X1 : G, (k X1 X0) ≠ (τ (σ (k X0 X1))) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq30164 X0 X1
       have i₂ := eq8 X1
       grind)
    | exact superpose eq8 eq30164
    | (have j0 := eq30164 X0 X1
       grind)
    | exact resolve eq30164 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30164
  have eq30176 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq30171 X0 X1
       have i₂ := eq8 (k X0 X1)
       grind)
    | exact superpose eq8 eq30171
    | (have j0 := eq30171 X0 X1
       grind)
    | (have r₁ := eq30171 X1 X1
       have r₂ := eq8 (k X1 X1)
       grind)
    | exact resolve eq30171 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30171
  have eq30180 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) X1) ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq30176 X0 X1
       have i₂ := eq8 X1
       grind)
    | exact superpose eq8 eq30176
    | (have j0 := eq30176 X0 X1
       grind)
    | exact resolve eq30176 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30176
  have eq30182 : ∀ X0 X1 : G, (M.op X0 X1) = (τ (σ (k X0 X1))) ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq30180 X0 X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq30180
    | (have j0 := eq30180 X0 X1
       grind)
    | exact resolve eq30180 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30180
  have eq30184 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq30182 X0 X1
       have i₂ := eq8 (k X0 X1)
       grind)
    | exact superpose eq8 eq30182
    | (have j0 := eq30182 X0 X1
       grind)
    | exact resolve eq30182 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30182
  have eq30271 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq30184 X0 X1
       have i₂ := eq1469 X0 X1
       grind)
    | exact superpose eq1469 eq30184
    | (have j0 := eq30184 X1 X0
       have j1 := eq1469 X1 X0
       grind)
    | exact resolve eq30184 eq1469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30184
  have eq30353 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq30271 X0 X1
       have j1 := eq1709 X1 X0
       grind)
    | (have r₁ := eq30271 X0 X1
       have r₂ := eq1709 X0 X1
       grind)
    | (have r₁ := eq30271 X1 X0
       have r₂ := eq1709 X0 X1
       grind)
    | exact resolve eq30271 eq1709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1709 eq30271
  have eq30475 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq30353 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq30353
    | (have j0 := eq30353 (σ X0) (σ X1)
       grind)
    | exact resolve eq30353 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30353
  have eq30515 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq30475 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq30475
    | (have j0 := eq30475 X0 X1
       grind)
    | exact resolve eq30475 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30475
  have eq30831 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (k (σ X1) (σ X0))) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq30027 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq30027
    | exact resolve eq30027 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30027
  have eq30866 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (k (τ (σ X1)) X0) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq30831 X0 X1
       have i₂ := eq20 (σ X1) X0
       grind)
    | exact superpose eq20 eq30831
    | (have j0 := eq30831 X0 X1
       grind)
    | exact resolve eq30831 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq30831
  have eq30873 : ∀ X0 X1 : G, (k X1 X0) ≠ (τ (σ (k X0 X1))) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq30866 X0 X1
       have i₂ := eq8 X1
       grind)
    | exact superpose eq8 eq30866
    | (have j0 := eq30866 X0 X1
       grind)
    | exact resolve eq30866 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30866
  have eq30877 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq30873 X0 X1
       have i₂ := eq8 (k X0 X1)
       grind)
    | exact superpose eq8 eq30873
    | (have j0 := eq30873 X0 X1
       grind)
    | (have r₁ := eq30873 X1 X1
       have r₂ := eq8 (k X1 X1)
       grind)
    | exact resolve eq30873 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30873
  have eq30879 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) X0) ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq30877 X0 X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq30877
    | (have j0 := eq30877 X0 X1
       grind)
    | exact resolve eq30877 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30877
  have eq30881 : ∀ X0 X1 : G, (M.op X1 X0) = (τ (σ (k X0 X1))) ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq30879 X0 X1
       have i₂ := eq8 X1
       grind)
    | exact superpose eq8 eq30879
    | (have j0 := eq30879 X0 X1
       grind)
    | exact resolve eq30879 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30879
  have eq30883 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq30881 X0 X1
       have i₂ := eq8 (k X0 X1)
       grind)
    | exact superpose eq8 eq30881
    | (have j0 := eq30881 X0 X1
       grind)
    | exact resolve eq30881 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30881
  have eq30913 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq30883 X0 X1
       have i₂ := eq1469 X0 X1
       grind)
    | exact superpose eq1469 eq30883
    | (have j0 := eq30883 X0 X1
       have j1 := eq1469 X0 X1
       grind)
    | exact resolve eq30883 eq1469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1469 eq30883
  have eq31001 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq30913 X0 X1
       have j1 := eq198 X0 X1
       grind)
    | (have r₁ := eq30913 X1 X0
       have r₂ := eq198 X0 X1
       grind)
    | (have r₁ := eq30913 X0 X1
       have r₂ := eq198 X0 X1
       grind)
    | exact resolve eq30913 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq30913
  have eq31493 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1453 x y
       grind)
    | exact superpose eq1453 eq14
    | (have j1 := eq1453 x y
       grind)
    | exact resolve eq14 eq1453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1453
  have eq32314 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq102 X0
       have i₂ := eq3229 (σ X0) X1
       grind)
    | exact superpose eq3229 eq102
    | (have j1 := eq3229 (σ X0) X1
       grind)
    | exact resolve eq102 eq3229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3229
  have eq32361 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq32314 X0 X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq32314
    | (have j0 := eq32314 X0 X1
       grind)
    | exact resolve eq32314 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32314
  have eq32378 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq32361 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq32361
    | (have j0 := eq32361 X0 X1
       grind)
    | exact resolve eq32361 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32361
  have eq33336 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op y y) ∨ (M.op X0 (σ x)) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq12150 y x X0
       grind)
    | exact superpose eq12150 eq14
    | (have j1 := eq12150 y x X0
       grind)
    | exact resolve eq14 eq12150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12150
  have eq33355 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ x) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq33336 X0
       have j1 := eq3172 x X0 y
       grind)
    | (have r₁ := eq33336 X0
       have r₂ := eq3172 x x y
       grind)
    | exact resolve eq33336 eq3172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3172 eq33336
  have eq33433 : ∀ X0 : G, (M.op X0 (σ x)) ≠ (M.op X0 (σ x)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq31001 X0 (σ x)
       have i₂ := eq33355 X0
       grind)
    | exact superpose eq33355 eq31001
    | (have j0 := eq31001 X0 (σ x)
       grind)
    | (have r₁ := eq31001 X0 (σ x)
       have r₂ := eq33355 X0
       grind)
    | exact resolve eq31001 eq33355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33355
  have eq33461 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq33433 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33433
  have eq33511 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op x x) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq12896 x y X0
       grind)
    | exact superpose eq12896 eq14
    | (have j1 := eq12896 x y X0
       grind)
    | exact resolve eq14 eq12896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12896
  have eq33530 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq33511 X0
       have j1 := eq3160 y X0 x
       grind)
    | (have r₁ := eq33511 X0
       have r₂ := eq3160 y x x
       grind)
    | exact resolve eq33511 eq3160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3160 eq33511
  have eq33605 : ∀ X0 : G, (M.op (σ y) X0) ≠ (M.op (σ y) X0) ∨ (M.op X0 (σ y)) = (k (σ y) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq31001 (σ y) X0
       have i₂ := eq33530 X0
       grind)
    | exact superpose eq33530 eq31001
    | (have j0 := eq31001 (σ y) X0
       grind)
    | (have r₁ := eq31001 (σ y) X0
       have r₂ := eq33530 X0
       grind)
    | exact resolve eq31001 eq33530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31001 eq33530
  have eq33639 : ∀ X0 : G, (M.op X0 (σ y)) = (k (σ y) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq33605 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33605
  have eq33782 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq33461 (σ X0)
       grind)
    | exact superpose eq33461 eq13
    | exact resolve eq13 eq33461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33461
  have eq33911 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq33639 (σ X0)
       grind)
    | exact superpose eq33639 eq13
    | exact resolve eq13 eq33639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33639
  have eq36157 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq33782 y
       grind)
    | exact superpose eq33782 eq14
    | exact resolve eq14 eq33782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33782
  have eq36519 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq33911 x
       grind)
    | exact superpose eq33911 eq14
    | exact resolve eq14 eq33911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33911
  have eq149957 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X0 X0)
       have i₂ := eq216 X0 X1
       grind)
    | exact superpose eq216 eq8
    | (have j1 := eq216 X0 X1
       grind)
    | exact resolve eq8 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq149966 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq149957 X0 X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq149957
    | (have j0 := eq149957 X0 X1
       grind)
    | exact resolve eq149957 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149957
  have eq150002 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X0 ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq149966 X0 (σ X1)
       grind)
    | exact superpose eq149966 eq13
    | (have j1 := eq149966 X0 X0
       grind)
    | exact resolve eq13 eq149966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149966
  have eq150013 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq150002 X0 X1
       have i₂ := eq102 X1
       grind)
    | exact superpose eq102 eq150002
    | (have j0 := eq150002 X0 X1
       grind)
    | exact resolve eq150002 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq150002
  have eq223956 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq150013 x y
       grind)
    | exact superpose eq150013 eq14
    | (have j1 := eq150013 x y
       grind)
    | exact resolve eq14 eq150013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150013
  have eq223957 : (σ y) = (σ (M.op y y)) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq32378 y x
       grind)
    | (have r₁ := eq223956
       have r₂ := eq32378 y x
       grind)
    | exact resolve eq223956 eq32378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32378 eq223956
  have eq223971 : (M.op y y) = (τ (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq8 (M.op y y)
       have i₂ := eq223957
       grind)
    | exact superpose eq223957 eq8
    | exact resolve eq8 eq223957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223957
  have eq224034 : y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq223971
       have i₂ := eq8 y
       grind)
    | exact superpose eq8 eq223971
    | exact resolve eq223971 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223971
  have eq224037 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k y X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq224034
       grind)
    | exact superpose eq224034 eq10
    | (have j0 := eq10 y X0
       grind)
    | (have r₁ := eq10 y x
       have r₂ := eq224034
       grind)
    | (have r₁ := eq10 x x
       have r₂ := eq224034
       grind)
    | exact resolve eq10 eq224034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224034
  have eq224078 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq224037 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224037
  have eq224327 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq36519
       have i₂ := eq224078 x
       grind)
    | exact superpose eq224078 eq36519
    | exact resolve eq36519 eq224078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36519 eq224078
  have eq224402 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) := by grind
  clear eq224327
  have eq224403 : x = (M.op x x) := by grind
  clear eq224402
  have eq224434 : ∀ X0 : G, x ≠ x ∨ (M.op X0 x) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq224403
       grind)
    | exact superpose eq224403 eq10
    | (have j0 := eq10 x X0
       grind)
    | (have r₁ := eq10 x x
       have r₂ := eq224403
       grind)
    | exact resolve eq10 eq224403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224436 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 (σ x)) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq214 x X0
       have i₂ := eq224403
       grind)
    | exact superpose eq224403 eq214
    | (have j0 := eq214 x X0
       grind)
    | exact resolve eq214 eq224403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq224442 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq2166 x X0
       have i₂ := eq224403
       grind)
    | exact superpose eq224403 eq2166
    | (have j0 := eq2166 x X0
       grind)
    | (have r₁ := eq2166 x x
       have r₂ := eq224403
       grind)
    | exact resolve eq2166 eq224403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224403
  have eq224467 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq224442 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224442
  have eq224473 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq224436 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224436
  have eq224475 : ∀ X0 : G, (M.op X0 x) = (k x X0) := by
    intro X0
    first
    | (have j0 := eq224434 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224434
  have eq224886 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq31493
       have i₂ := eq224467 y
       grind)
    | exact superpose eq224467 eq31493
    | exact resolve eq31493 eq224467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31493
  have eq224891 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq36157
       have i₂ := eq224467 y
       grind)
    | exact superpose eq224467 eq36157
    | exact resolve eq36157 eq224467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36157
  have eq224909 : y = (M.op y y) := by grind
  clear eq224891
  have eq224910 : (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
  clear eq224886
  have eq224917 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq224910
       have i₂ := eq224475 y
       grind)
    | exact superpose eq224475 eq224910
    | exact resolve eq224910 eq224475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224910
  have eq225026 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq2166 y X0
       have i₂ := eq224909
       grind)
    | exact superpose eq224909 eq2166
    | (have j0 := eq2166 y X0
       grind)
    | (have r₁ := eq2166 y x
       have r₂ := eq224909
       grind)
    | exact resolve eq2166 eq224909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2166 eq224909
  have eq225051 : ∀ X0 : G, (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq225026 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225026
  have eq228408 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq224473 (σ X0)
       grind)
    | exact superpose eq224473 eq13
    | exact resolve eq13 eq224473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224473
  have eq228639 : ∀ X0 : G, (σ (M.op X0 x)) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq228408 X0
       have i₂ := eq224475 X0
       grind)
    | exact superpose eq224475 eq228408
    | exact resolve eq228408 eq224475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224475 eq228408
  have eq230648 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq224917
       grind)
    | exact superpose eq224917 eq14
    | exact resolve eq14 eq224917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230720 : (σ (k x y)) ≠ (σ (M.op y x)) ∨ (σ (k y x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq30515 x y
       have i₂ := eq224917
       grind)
    | exact superpose eq224917 eq30515
    | (have j0 := eq30515 x y
       grind)
    | exact resolve eq30515 eq224917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30515 eq224917
  have eq230780 : (σ (M.op y x)) ≠ (σ (M.op y x)) ∨ (σ (k y x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq230720
       have i₂ := eq225051 x
       grind)
    | exact superpose eq225051 eq230720
    | exact resolve eq230720 eq225051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225051 eq230720
  have eq230781 : (σ (k y x)) = (M.op (σ y) (σ x)) := by grind
  clear eq230780
  have eq230799 : (σ (k y x)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq230781
       have i₂ := eq228639 y
       grind)
    | exact superpose eq228639 eq230781
    | exact resolve eq230781 eq228639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228639 eq230781
  have eq230810 : (σ (M.op x y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq230799
       have i₂ := eq224467 y
       grind)
    | exact superpose eq224467 eq230799
    | exact resolve eq230799 eq224467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224467 eq230799
  have eq230820 : False := by grind
  exact eq230820

/-- `x □ y = if m(X,X) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_x_x_y_pxy_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq8
    | exact resolve eq8 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq33 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq34 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq33 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq33
    | (have j0 := eq33 X0
       grind)
    | exact resolve eq33 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq36 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq21
    | exact resolve eq21 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq51 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X2) = (M.op X0 X2) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X0 X2
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X1
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X1 X1
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X0 X2) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq51 X0 X2 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq81 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq82 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq81 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq82 (σ X0) (σ X1)
       grind)
    | exact superpose eq82 eq13
    | (have j1 := eq82 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq13 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq82 (τ X0) X1
       grind)
    | exact superpose eq82 eq16
    | (have j1 := eq82 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq16 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq82
  have eq95 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq31 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq87 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq87
    | exact resolve eq87 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq252 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq226 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq226
    | (have j0 := eq226 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq226 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq402 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq95 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq95
    | (have j0 := eq95 (τ X0)
       grind)
    | exact resolve eq95 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq95
  have eq403 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq402 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq402
    | (have j0 := eq402 X0
       grind)
    | exact resolve eq402 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq406 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq403 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq403
    | (have j0 := eq403 X0
       grind)
    | exact resolve eq403 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq413 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq406 (τ X0)
       have i₂ := eq36 X0 X0
       grind)
    | exact superpose eq36 eq406
    | (have j0 := eq406 (τ X0)
       grind)
    | exact resolve eq406 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq406
  have eq432 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq34
    | exact resolve eq34 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq457 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq432 X0
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq432
    | (have j0 := eq432 X0
       grind)
    | exact resolve eq432 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq1163 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq85 x y
       grind)
    | exact superpose eq85 eq14
    | (have j1 := eq85 x y
       grind)
    | exact resolve eq14 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq1245 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1163
       have i₂ := eq252 x y
       grind)
    | exact superpose eq252 eq1163
    | (have j1 := eq252 (σ x) (σ y)
       grind)
    | (have r₁ := eq1163
       have r₂ := eq252 x y
       grind)
    | (have r₁ := eq1163
       have r₂ := eq252 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1163
       have r₂ := eq252 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1163 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252 eq1163
  have eq1246 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1245
  have eq1326 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq1246
       grind)
    | exact superpose eq1246 eq8
    | exact resolve eq8 eq1246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1246
  have eq1374 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1326
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq1326
    | exact resolve eq1326 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326
  have eq1375 : x = y := by grind
  clear eq1374
  have eq1451 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1375
       grind)
    | exact superpose eq1375 eq14
    | exact resolve eq14 eq1375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1375
  have eq1575 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1451
       have i₂ := eq31 x
       grind)
    | exact superpose eq31 eq1451
    | (have j1 := eq31 x
       grind)
    | exact resolve eq1451 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq9973 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1575
       have i₂ := eq457 x
       grind)
    | exact superpose eq457 eq1575
    | (have j1 := eq457 (σ x)
       grind)
    | (have r₁ := eq1575
       have r₂ := eq457 x
       grind)
    | exact resolve eq1575 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq9974 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq9973
  have eq10116 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq10 (σ x) X0
       have i₂ := eq9974
       grind)
    | exact superpose eq9974 eq10
    | (have j0 := eq10 (σ x) X0
       grind)
    | (have r₁ := eq10 (σ x) x
       have r₂ := eq9974
       grind)
    | (have r₁ := eq10 x x
       have r₂ := eq9974
       grind)
    | exact resolve eq10 eq9974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10117 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq10116 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10116
  have eq10344 : (τ (σ x)) ≠ (τ (M.op (σ x) (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq413 (σ x)
       have i₂ := eq10117 (σ x)
       grind)
    | exact superpose eq10117 eq413
    | (have j0 := eq413 (σ x)
       grind)
    | exact resolve eq413 eq10117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413 eq10117
  have eq10398 : x ≠ (τ (M.op (σ x) (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10344
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq10344
    | exact resolve eq10344 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10344
  have eq10401 : x = (M.op x x) ∨ x ≠ (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10398
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq10398
    | exact resolve eq10398 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10398
  have eq10402 : x ≠ (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by grind
  clear eq10401
  have eq10581 : x ≠ (τ (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10402
       have i₂ := eq9974
       grind)
    | exact superpose eq9974 eq10402
    | exact resolve eq10402 eq9974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9974 eq10402
  have eq10587 : x ≠ (τ (σ x)) ∨ x = (M.op x x) := by grind
  clear eq10581
  have eq10588 : x = (M.op x x) := by
    first
    | (have r₁ := eq10587
       have r₂ := eq8 x
       grind)
    | exact resolve eq10587 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10587
  have eq10911 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq10588
       grind)
    | exact superpose eq10588 eq10
    | (have j0 := eq10 x X0
       grind)
    | (have r₁ := eq10 x x
       have r₂ := eq10588
       grind)
    | exact resolve eq10 eq10588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10912 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq10911 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10911
  have eq11238 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1575
       have i₂ := eq10912 x
       grind)
    | exact superpose eq10912 eq1575
    | exact resolve eq1575 eq10912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1575 eq10912
  have eq11282 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq11238
  have eq11592 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1451
       have i₂ := eq11282
       grind)
    | exact superpose eq11282 eq1451
    | exact resolve eq1451 eq11282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1451 eq11282
  have eq11595 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq11592
       have i₂ := eq10588
       grind)
    | exact superpose eq10588 eq11592
    | exact resolve eq11592 eq10588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10588 eq11592
  have eq11596 : False := by grind
  exact eq11596

/-- `x □ y = if m(X,X) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_x_x_y_pyx_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq8
    | exact resolve eq8 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq33 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq34 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq33 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq33
    | (have j0 := eq33 X0
       grind)
    | exact resolve eq33 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq36 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq21
    | exact resolve eq21 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq51 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X2) = (M.op X2 X0) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X0 X2
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X1
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X1 X1
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X2 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq51 X0 X2 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq81 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq82 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq81 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq85 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq82 (σ X1) (σ X0)
       grind)
    | exact superpose eq82 eq13
    | (have j1 := eq82 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq13 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq82 (τ X1) X0
       grind)
    | exact superpose eq82 eq16
    | (have j1 := eq82 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq16 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq82
  have eq95 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq31 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq87
    | exact resolve eq87 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq251 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq225 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq225
    | (have j0 := eq225 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq225 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq401 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq95 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq95
    | (have j0 := eq95 (τ X0)
       grind)
    | exact resolve eq95 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq95
  have eq402 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq401 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq401
    | (have j0 := eq401 X0
       grind)
    | exact resolve eq401 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq405 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq402 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq402
    | (have j0 := eq402 X0
       grind)
    | exact resolve eq402 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq412 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq405 (τ X0)
       have i₂ := eq36 X0 X0
       grind)
    | exact superpose eq36 eq405
    | (have j0 := eq405 (τ X0)
       grind)
    | exact resolve eq405 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq405
  have eq431 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq34
    | exact resolve eq34 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq456 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq431 X0
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq431
    | (have j0 := eq431 X0
       grind)
    | exact resolve eq431 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq1221 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq85 x y
       grind)
    | exact superpose eq85 eq14
    | (have j1 := eq85 x y
       grind)
    | exact resolve eq14 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq1308 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1221
       have i₂ := eq251 y x
       grind)
    | exact superpose eq251 eq1221
    | (have j1 := eq251 (σ x) (σ y)
       grind)
    | (have r₁ := eq1221
       have r₂ := eq251 y x
       grind)
    | (have r₁ := eq1221
       have r₂ := eq251 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1221
       have r₂ := eq251 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1221 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251 eq1221
  have eq1309 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1308
  have eq1390 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq1309
       grind)
    | exact superpose eq1309 eq8
    | exact resolve eq8 eq1309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1309
  have eq1438 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1390
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq1390
    | exact resolve eq1390 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1390
  have eq1439 : x = y := by grind
  clear eq1438
  have eq1562 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1439
       grind)
    | exact superpose eq1439 eq14
    | exact resolve eq14 eq1439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439
  have eq1661 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1562
       have i₂ := eq31 x
       grind)
    | exact superpose eq31 eq1562
    | (have j1 := eq31 x
       grind)
    | exact resolve eq1562 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq9953 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1661
       have i₂ := eq456 x
       grind)
    | exact superpose eq456 eq1661
    | (have j1 := eq456 (σ x)
       grind)
    | (have r₁ := eq1661
       have r₂ := eq456 x
       grind)
    | exact resolve eq1661 eq456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq9954 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq9953
  have eq10096 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq10 (σ x) X0
       have i₂ := eq9954
       grind)
    | exact superpose eq9954 eq10
    | (have j0 := eq10 (σ x) X0
       grind)
    | (have r₁ := eq10 (σ x) x
       have r₂ := eq9954
       grind)
    | (have r₁ := eq10 x x
       have r₂ := eq9954
       grind)
    | exact resolve eq10 eq9954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10097 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq10096 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10096
  have eq10324 : (τ (σ x)) ≠ (τ (M.op (σ x) (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq412 (σ x)
       have i₂ := eq10097 (σ x)
       grind)
    | exact superpose eq10097 eq412
    | (have j0 := eq412 (σ x)
       grind)
    | exact resolve eq412 eq10097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412 eq10097
  have eq10378 : x ≠ (τ (M.op (σ x) (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10324
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq10324
    | exact resolve eq10324 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10324
  have eq10381 : x = (M.op x x) ∨ x ≠ (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10378
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq10378
    | exact resolve eq10378 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10378
  have eq10382 : x ≠ (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by grind
  clear eq10381
  have eq10561 : x ≠ (τ (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10382
       have i₂ := eq9954
       grind)
    | exact superpose eq9954 eq10382
    | exact resolve eq10382 eq9954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9954 eq10382
  have eq10566 : x ≠ (τ (σ x)) ∨ x = (M.op x x) := by grind
  clear eq10561
  have eq10567 : x = (M.op x x) := by
    first
    | (have r₁ := eq10566
       have r₂ := eq8 x
       grind)
    | exact resolve eq10566 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10566
  have eq10890 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq10567
       grind)
    | exact superpose eq10567 eq10
    | (have j0 := eq10 x X0
       grind)
    | (have r₁ := eq10 x x
       have r₂ := eq10567
       grind)
    | exact resolve eq10 eq10567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10891 : ∀ X0 : G, (k x X0) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq10890 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10890
  have eq11214 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1661
       have i₂ := eq10891 x
       grind)
    | exact superpose eq10891 eq1661
    | exact resolve eq1661 eq10891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1661 eq10891
  have eq11258 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq11214
  have eq11565 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1562
       have i₂ := eq11258
       grind)
    | exact superpose eq11258 eq1562
    | exact resolve eq1562 eq11258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1562 eq11258
  have eq11568 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq11565
       have i₂ := eq10567
       grind)
    | exact superpose eq10567 eq11565
    | exact resolve eq11565 eq10567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10567 eq11565
  have eq11569 : False := by grind
  exact eq11569
