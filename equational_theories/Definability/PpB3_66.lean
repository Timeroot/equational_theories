import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4209`: `x ◇ y = ((z ◇ y) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyy_pyx_Equation4209 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4209 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4209.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X2 X1) X0) X1) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq25 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op x X1)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq79 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq25 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq25
    | exact resolve eq25 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq47 y x
       grind)
    | exact superpose eq47 eq16
    | (have j1 := eq47 y x
       grind)
    | exact resolve eq16 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ X1) (σ X0)
       have i₂ := eq47 X0 X1
       grind)
    | exact superpose eq47 eq25
    | (have j1 := eq47 X0 X1
       grind)
    | exact resolve eq25 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq549 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq108
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq108
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq108
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq108
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq108 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq550 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq549
  have eq1391 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) ≠ (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq113 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq113
    | exact resolve eq113 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq1412 : ∀ X0 X1 : G, (k (σ X1) X0) ≠ (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1391 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq1391
    | (have j0 := eq1391 X0 X1
       grind)
    | exact resolve eq1391 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1391
  have eq4177 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1412 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1412
    | exact resolve eq1412 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412
  have eq6182 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq550
       grind)
    | exact superpose eq550 eq16
    | exact resolve eq16 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq6183 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq6182
       have r₂ := eq22 x
       grind)
    | exact resolve eq6182 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6182
  have eq28965 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq6183
       grind)
    | exact superpose eq6183 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq6183
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq6183
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq6183
       grind)
    | exact resolve eq13 eq6183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28966 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq25 y x
       have i₂ := eq6183
       grind)
    | exact superpose eq6183 eq25
    | exact resolve eq25 eq6183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6183
  have eq28979 : x = y ∨ (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq28965
  have eq651327 : (M.op y y) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq9 y y x
       have i₂ := eq28966
       grind)
    | exact superpose eq28966 eq9
    | exact resolve eq9 eq28966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq679693 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq28966
       have i₂ := eq651327
       grind)
    | exact superpose eq651327 eq28966
    | exact resolve eq28966 eq651327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28966 eq651327
  have eq679789 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq679693
  have eq679827 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq679789
       grind)
    | exact superpose eq679789 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq679789
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq679789
       grind)
    | exact resolve eq13 eq679789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679789
  have eq679887 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq679827
  have eq679888 : (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq679887
  have eq679902 : (σ (M.op y y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq679888
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq679888
    | exact resolve eq679888 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679888
  have eq679907 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq679902
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq679902
    | exact resolve eq679902 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679902
  have eq777401 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq28979
       grind)
    | exact superpose eq28979 eq16
    | exact resolve eq16 eq28979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28979
  have eq777402 : (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq777401
       have r₂ := eq22 x
       grind)
    | exact resolve eq777401 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777401
  have eq779062 : (M.op (σ x) (σ y)) = (M.op (σ (M.op y y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq109 x y
       have i₂ := eq777402
       grind)
    | exact superpose eq777402 eq109
    | (have j0 := eq109 y x
       grind)
    | exact resolve eq109 eq777402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq777402
  have eq779194 : (M.op (σ x) (σ y)) = (M.op (σ (M.op y y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq779062
  have eq779211 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq779194
       have i₂ := eq79 y
       grind)
    | exact superpose eq79 eq779194
    | exact resolve eq779194 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779194
  have eq844240 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq779211
       grind)
    | exact superpose eq779211 eq16
    | exact resolve eq16 eq779211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779211
  have eq846625 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq844240
       have i₂ := eq679907
       grind)
    | exact superpose eq679907 eq844240
    | exact resolve eq844240 eq679907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679907 eq844240
  have eq846635 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op y y)) := by grind
  clear eq846625
  have eq846636 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op y y)) := by grind
  clear eq846635
  have eq974536 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq846636
       grind)
    | exact superpose eq846636 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq846636
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq846636
       grind)
    | exact resolve eq13 eq846636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846636
  have eq974608 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (k x y)) = (σ (M.op y y)) := by grind
  clear eq974536
  have eq974609 : (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (k x y)) = (σ (M.op y y)) := by grind
  clear eq974608
  have eq974634 : (σ (M.op y y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq974609
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq974609
    | exact resolve eq974609 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974609
  have eq974644 : (σ (k x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq974634
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq974634
    | exact resolve eq974634 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974634
  have eq974645 : (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op y y)) := by grind
  clear eq974644
  have eq977101 : y = (τ (σ x)) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq974645
       grind)
    | exact superpose eq974645 eq10
    | exact resolve eq10 eq974645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974645
  have eq978033 : x = y ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq977101
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq977101
    | exact resolve eq977101 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977101
  have eq980570 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq978033
       grind)
    | exact superpose eq978033 eq16
    | exact resolve eq16 eq978033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978033
  have eq980641 : (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq980570
       have r₂ := eq22 x
       grind)
    | exact resolve eq980570 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980570
  have eq983287 : (k x y) = (τ (σ (M.op y y))) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq980641
       grind)
    | exact superpose eq980641 eq10
    | exact resolve eq10 eq980641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980641
  have eq984219 : (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq983287
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq983287
    | exact resolve eq983287 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq983287
  have eq984243 : x = y ∨ (M.op x y) = (M.op y x) ∨ (M.op y x) = (M.op y y) := by
    first
    | (have i₁ := eq984219
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq984219
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq984219 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq984299 : (M.op x y) ≠ (M.op y y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq4177 x y
       have i₂ := eq984219
       grind)
    | exact superpose eq984219 eq4177
    | (have j0 := eq4177 x y
       grind)
    | exact resolve eq4177 eq984219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4177 eq984219
  have eq993403 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op y x) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq984243
       grind)
    | exact superpose eq984243 eq16
    | exact resolve eq16 eq984243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984243
  have eq993476 : (M.op x y) = (M.op y x) ∨ (M.op y x) = (M.op y y) := by
    first
    | (have r₁ := eq993403
       have r₂ := eq22 x
       grind)
    | exact resolve eq993403 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993403
  have eq995683 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op y x) = (M.op y y) := by
    first
    | (have i₁ := eq25 y x
       have i₂ := eq993476
       grind)
    | exact superpose eq993476 eq25
    | exact resolve eq25 eq993476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993476
  have eq995775 : (M.op y y) = (M.op (M.op x y) y) ∨ (M.op y x) = (M.op y y) := by
    first
    | (have i₁ := eq9 y y x
       have i₂ := eq995683
       grind)
    | exact superpose eq995683 eq9
    | exact resolve eq9 eq995683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq995889 : (M.op x y) = (M.op y y) ∨ (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op y y) := by
    first
    | (have i₁ := eq995683
       have i₂ := eq995775
       grind)
    | exact superpose eq995775 eq995683
    | exact resolve eq995683 eq995775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995683 eq995775
  have eq996001 : (M.op y x) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq995889
  have eq996340 : (M.op y x) = (M.op (M.op y x) y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq25 y y
       have i₂ := eq996001
       grind)
    | exact superpose eq996001 eq25
    | exact resolve eq25 eq996001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq996408 : (M.op x y) ≠ (M.op y x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq996001
  have eq996415 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq996340
       have i₂ := eq25 y x
       grind)
    | exact superpose eq25 eq996340
    | exact resolve eq996340 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996340
  have eq996427 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq996415
       have r₂ := eq996408
       grind)
    | exact resolve eq996415 eq996408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996408 eq996415
  have eq996448 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq79 y
       have i₂ := eq996427
       grind)
    | exact superpose eq996427 eq79
    | exact resolve eq79 eq996427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1047185 : (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq984299
       have r₂ := eq996427
       grind)
    | exact resolve eq984299 eq996427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984299 eq996427
  have eq1047187 : ∀ X0 : G, x = y ∨ (M.op X0 x) = (M.op (M.op (M.op x y) X0) x) := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq1047185
       grind)
    | exact superpose eq1047185 eq9
    | exact resolve eq9 eq1047185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1049171 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 x) = (M.op (M.op (M.op x y) X0) x) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq1047187 X0
       grind)
    | exact superpose eq1047187 eq16
    | (have j1 := eq1047187 X0
       grind)
    | exact resolve eq16 eq1047187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047187
  have eq1049266 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op (M.op x y) X0) x) := by
    intro X0
    first
    | (have j0 := eq1049171 X0
       grind)
    | (have r₁ := eq1049171 X0
       have r₂ := eq22 x
       grind)
    | exact resolve eq1049171 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049171
  have eq1049286 : (M.op x x) = (M.op (M.op y x) x) := by
    first
    | (have i₁ := eq1049266 x
       have i₂ := eq25 x y
       grind)
    | exact superpose eq25 eq1049266
    | exact resolve eq1049266 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049266
  have eq1051398 : (M.op x x) = (M.op (M.op x y) x) ∨ x = y := by
    first
    | (have i₁ := eq1049286
       have i₂ := eq1047185
       grind)
    | exact superpose eq1047185 eq1049286
    | exact resolve eq1049286 eq1047185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049286
  have eq1051530 : (M.op y x) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq1051398
       have i₂ := eq25 x y
       grind)
    | exact superpose eq25 eq1051398
    | exact resolve eq1051398 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1051398
  have eq1051537 : (M.op x y) = (M.op x x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq1047185
       have i₂ := eq1051530
       grind)
    | exact superpose eq1051530 eq1047185
    | exact resolve eq1047185 eq1051530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047185 eq1051530
  have eq1051655 : x = y ∨ (M.op x y) = (M.op x x) := by grind
  clear eq1051537
  have eq1053674 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1051655
       grind)
    | exact superpose eq1051655 eq16
    | exact resolve eq16 eq1051655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1051655
  have eq1053771 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq1053674
       have r₂ := eq22 x
       grind)
    | exact resolve eq1053674 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1053674
  have eq1053786 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ y)) := by
    first
    | (have i₁ := eq996448
       have i₂ := eq1053771
       grind)
    | exact superpose eq1053771 eq996448
    | exact resolve eq996448 eq1053771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996448
  have eq1074379 : (M.op (σ y) (σ x)) = (M.op (σ (M.op x x)) (σ x)) := by
    first
    | (have i₁ := eq80 x (σ y)
       have i₂ := eq1053786
       grind)
    | exact superpose eq1053786 eq80
    | exact resolve eq80 eq1053786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq1074665 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1074379
       have i₂ := eq79 x
       grind)
    | exact superpose eq79 eq1074379
    | exact resolve eq1074379 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq1074379
  have eq1075067 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x x)) (σ y)) := by
    first
    | (have i₁ := eq25 (σ y) (σ x)
       have i₂ := eq1074665
       grind)
    | exact superpose eq1074665 eq25
    | exact resolve eq25 eq1074665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1074665
  have eq1075194 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1075067
       have i₂ := eq1053786
       grind)
    | exact superpose eq1053786 eq1075067
    | exact resolve eq1075067 eq1053786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053786 eq1075067
  have eq1078189 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1075194
       grind)
    | exact superpose eq1075194 eq16
    | exact resolve eq16 eq1075194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075194
  have eq1078425 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1078189
       have i₂ := eq1053771
       grind)
    | exact superpose eq1053771 eq1078189
    | exact resolve eq1078189 eq1053771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053771 eq1078189
  have eq1078426 : False := by grind
  exact eq1078426

/-- `Equation4209`: `x ◇ y = ((z ◇ y) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_y_pyx_Equation4209 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4209 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4209.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X2 X1) X0) X1) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op x X1)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq109 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq109
    | exact resolve eq109 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op X0 X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq109 (M.op X1 X0) X1
       have i₂ := eq109 X1 X0
       grind)
    | exact superpose eq109 eq109
    | exact resolve eq109 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq109 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq110 X0
       grind)
    | exact superpose eq110 eq109
    | exact resolve eq109 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq123 X0
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq123
    | exact resolve eq123 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq132 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq125 X0
       have i₂ := eq113 X0 X0
       grind)
    | exact superpose eq113 eq125
    | exact resolve eq125 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq125
  have eq396 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op X1 (σ X0)) = X1 ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq28
    | (have j1 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq397 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq398 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq741 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq398 x y
       grind)
    | exact superpose eq398 eq16
    | (have j1 := eq398 x y
       grind)
    | exact resolve eq16 eq398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq748 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq398 X1 X0
       grind)
    | exact superpose eq398 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq398 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq398 X0 X1
       grind)
    | exact resolve eq13 eq398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq749 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq109 (σ X1) (σ X0)
       have i₂ := eq398 X1 X0
       grind)
    | exact superpose eq398 eq109
    | (have j1 := eq398 X1 X0
       grind)
    | exact resolve eq109 eq398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq752 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq748 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq753 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq752 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq752
    | (have j0 := eq752 X0 X1
       grind)
    | exact resolve eq752 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq9944 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq397 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq397
    | exact resolve eq397 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq10050 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9944 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq9944
    | (have j0 := eq9944 X0 X1
       grind)
    | exact resolve eq9944 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9944
  have eq10301 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq396 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq396
    | exact resolve eq396 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq10379 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10301 X0 X1
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq10301
    | (have j0 := eq10301 X0 X1
       grind)
    | exact resolve eq10301 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10301
  have eq19650 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq741
       have i₂ := eq10050 x y
       grind)
    | exact superpose eq10050 eq741
    | (have j1 := eq10050 (σ x) (σ y)
       grind)
    | (have r₁ := eq741
       have r₂ := eq10050 x y
       grind)
    | (have r₁ := eq741
       have r₂ := eq10050 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq741
       have r₂ := eq10050 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq741 eq10050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq19651 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq19650
  have eq24631 : ∀ X0 X1 : G, (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ (k X0 X1))) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq749 (τ X0) (τ X1)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq749
    | (have j0 := eq749 (τ X0) (τ X1)
       grind)
    | exact resolve eq749 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq749
  have eq24783 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = (M.op (σ (τ (k X0 X1))) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24631 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24631
    | (have j0 := eq24631 X0 X1
       grind)
    | exact resolve eq24631 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24631
  have eq24830 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = (M.op (k X0 X1) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24783 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq24783
    | (have j0 := eq24783 X0 X1
       grind)
    | exact resolve eq24783 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24783
  have eq24872 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (k X0 X1) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24830 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24830
    | (have j0 := eq24830 X0 X1
       grind)
    | exact resolve eq24830 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24830
  have eq24902 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X1) = (M.op (k X0 X1) X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24872 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq24872
    | (have j0 := eq24872 X0 X1
       grind)
    | exact resolve eq24872 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24872
  have eq24927 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (M.op (k X0 X1) X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24902 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24902
    | (have j0 := eq24902 X0 X1
       grind)
    | exact resolve eq24902 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24902
  have eq24952 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (M.op (k X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24927 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq24927
    | (have j0 := eq24927 X0 X1
       grind)
    | exact resolve eq24927 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24927
  have eq24965 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (k X0 X1) X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24952 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24952
    | (have j0 := eq24952 X0 X1
       grind)
    | exact resolve eq24952 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24952
  have eq54348 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19651
       grind)
    | exact superpose eq19651 eq16
    | exact resolve eq16 eq19651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19651
  have eq54349 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq54348
       have r₂ := eq22 x
       grind)
    | exact resolve eq54348 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54348
  have eq54351 : y ≠ y ∨ x = y ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq54349
       grind)
    | exact superpose eq54349 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq54349
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq54349
       grind)
    | exact resolve eq13 eq54349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54349
  have eq54380 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq54351
  have eq76165 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq54380
       grind)
    | exact superpose eq54380 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq54380
       grind)
    | exact resolve eq13 eq54380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54380
  have eq76196 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (k y x) ∨ x = y := by grind
  clear eq76165
  have eq76197 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (k y x) ∨ x = y := by grind
  clear eq76196
  have eq76218 : x = y ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq76197
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq76197
    | exact resolve eq76197 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76197
  have eq76234 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq76218
       grind)
    | exact superpose eq76218 eq16
    | exact resolve eq16 eq76218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76218
  have eq76241 : x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq76234
       have r₂ := eq22 x
       grind)
    | exact resolve eq76234 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76234
  have eq76248 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq753 y x
       have i₂ := eq76241
       grind)
    | exact superpose eq76241 eq753
    | (have j0 := eq753 y x
       grind)
    | (have r₁ := eq753 y x
       have r₂ := eq76241
       grind)
    | exact resolve eq753 eq76241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76241
  have eq76272 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq76248
  have eq76273 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq76272
  have eq76277 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have j1 := eq753 y x
       grind)
    | (have r₁ := eq76273
       have r₂ := eq753 x y
       grind)
    | (have r₁ := eq76273
       have r₂ := eq753 y x
       grind)
    | exact resolve eq76273 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753 eq76273
  have eq76280 : (σ y) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq398 y x
       have i₂ := eq76277
       grind)
    | exact superpose eq76277 eq398
    | (have j0 := eq398 y x
       grind)
    | exact resolve eq398 eq76277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398 eq76277
  have eq76320 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) := by grind
  clear eq76280
  have eq77403 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq76320
       grind)
    | exact superpose eq76320 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq76320
       grind)
    | exact resolve eq13 eq76320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76320
  have eq77433 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq77403
  have eq77434 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq77433
  have eq77454 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq77434
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq77434
    | exact resolve eq77434 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77434
  have eq77455 : (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq77454
  have eq77467 : y = (τ (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq77455
       grind)
    | exact superpose eq77455 eq10
    | exact resolve eq10 eq77455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77455
  have eq77554 : x = y ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq77467
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq77467
    | exact resolve eq77467 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77467
  have eq77556 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq77554
       grind)
    | exact superpose eq77554 eq16
    | exact resolve eq16 eq77554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77554
  have eq77584 : (σ y) = (σ (k x y)) := by
    first
    | (have r₁ := eq77556
       have r₂ := eq22 x
       grind)
    | exact resolve eq77556 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77556
  have eq77606 : x = (M.op x y) ∨ (σ y) = (σ (M.op y x)) ∨ x = y := by
    first
    | (have i₁ := eq10050 y x
       have i₂ := eq77584
       grind)
    | exact superpose eq77584 eq10050
    | (have j0 := eq10050 y x
       grind)
    | exact resolve eq10050 eq77584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10050
  have eq77609 : (k x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq77584
       grind)
    | exact superpose eq77584 eq10
    | exact resolve eq10 eq77584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77584
  have eq77698 : y = (k x y) := by
    first
    | (have i₁ := eq77609
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq77609
    | exact resolve eq77609 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77609
  have eq77718 : x = (M.op x y) ∨ (τ y) = (τ (M.op y x)) ∨ x = y := by
    first
    | (have i₁ := eq10379 y x
       have i₂ := eq77698
       grind)
    | exact superpose eq77698 eq10379
    | (have j0 := eq10379 y x
       grind)
    | exact resolve eq10379 eq77698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10379
  have eq77723 : x = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq24965 x y
       have i₂ := eq77698
       grind)
    | exact superpose eq77698 eq24965
    | (have j0 := eq24965 x y
       grind)
    | exact resolve eq24965 eq77698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24965 eq77698
  have eq79569 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op x X0) y) ∨ (τ y) = (τ (M.op y x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq77718
       grind)
    | exact superpose eq77718 eq9
    | exact resolve eq9 eq77718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77718
  have eq85401 : (M.op x y) = (M.op y y) ∨ (τ y) = (τ (M.op y x)) ∨ x = y ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq79569 y
       have i₂ := eq77723
       grind)
    | exact superpose eq77723 eq79569
    | exact resolve eq79569 eq77723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77723 eq79569
  have eq85459 : (τ y) = (τ (M.op y x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq85401
  have eq85474 : (M.op y x) = (σ (τ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq11 (M.op y x)
       have i₂ := eq85459
       grind)
    | exact superpose eq85459 eq11
    | exact resolve eq11 eq85459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85459
  have eq85640 : y = (M.op y x) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq85474
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq85474
    | exact resolve eq85474 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85474
  have eq85652 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq109 y x
       have i₂ := eq85640
       grind)
    | exact superpose eq85640 eq109
    | exact resolve eq109 eq85640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq85640
  have eq85682 : x = y ∨ (M.op x y) = (M.op y y) := by grind
  clear eq85652
  have eq85695 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq85682
       grind)
    | exact superpose eq85682 eq16
    | exact resolve eq16 eq85682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85682
  have eq85762 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq85695
       have r₂ := eq22 x
       grind)
    | exact resolve eq85695 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85695
  have eq85769 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq110 y
       have i₂ := eq85762
       grind)
    | exact superpose eq85762 eq110
    | exact resolve eq110 eq85762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq85762
  have eq86326 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op y x)) ∨ x = y := by
    first
    | (have i₁ := eq85769
       have i₂ := eq77606
       grind)
    | exact superpose eq77606 eq85769
    | exact resolve eq85769 eq77606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85769
  have eq97039 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (M.op y x)) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq86326
       grind)
    | exact superpose eq86326 eq16
    | exact resolve eq16 eq86326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86326
  have eq97115 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op y x)) ∨ x = y ∨ (σ y) = (σ (M.op y x)) ∨ x = y := by
    first
    | (have i₁ := eq97039
       have i₂ := eq77606
       grind)
    | exact superpose eq77606 eq97039
    | exact resolve eq97039 eq77606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77606 eq97039
  have eq97164 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op y x)) ∨ x = y := by grind
  clear eq97115
  have eq97165 : (σ y) = (σ (M.op y x)) ∨ x = y := by grind
  clear eq97164
  have eq97171 : (M.op y x) = (τ (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq10 (M.op y x)
       have i₂ := eq97165
       grind)
    | exact superpose eq97165 eq10
    | exact resolve eq10 eq97165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97165
  have eq97266 : y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq97171
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq97171
    | exact resolve eq97171 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97171
  have eq97278 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op y X0) x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq97266
       grind)
    | exact superpose eq97266 eq9
    | exact resolve eq9 eq97266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97355 : (M.op y x) = (M.op x x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq97278 x
       have i₂ := eq97266
       grind)
    | exact superpose eq97266 eq97278
    | exact resolve eq97278 eq97266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97278
  have eq97407 : (M.op y x) = (M.op x x) ∨ x = y := by grind
  clear eq97355
  have eq97460 : y = (M.op x x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq97266
       have i₂ := eq97407
       grind)
    | exact superpose eq97407 eq97266
    | exact resolve eq97266 eq97407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97266 eq97407
  have eq97499 : x = y ∨ y = (M.op x x) := by grind
  clear eq97460
  have eq97534 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq97499
       grind)
    | exact superpose eq97499 eq16
    | exact resolve eq16 eq97499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97499
  have eq97652 : y = (M.op x x) := by
    first
    | (have r₁ := eq97534
       have r₂ := eq22 x
       grind)
    | exact resolve eq97534 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq97534
  have eq97676 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq132 x
       have i₂ := eq97652
       grind)
    | exact superpose eq97652 eq132
    | exact resolve eq132 eq97652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq97652
  have eq97961 : False := by grind
  exact eq97961

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_pyy_pxy_Equation422 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law422 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq267 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq267 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq270 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq268 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq268 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq268 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq281 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq270 (σ X0)
       grind)
    | exact superpose eq270 eq15
    | exact resolve eq15 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq281 X0
       have i₂ := eq270 X0
       grind)
    | exact superpose eq270 eq281
    | exact resolve eq281 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270 eq281
  have eq345 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq300 X0
       grind)
    | exact superpose eq300 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq300 X0
       grind)
    | exact superpose eq300 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq347 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq345 X0 X1
       have j1 := eq346 X0 X1
       grind)
    | (have r₁ := eq345 X0 X1
       have r₂ := eq346 X0 X1
       grind)
    | exact resolve eq345 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345 eq346
  have eq410 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq347 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq347
    | exact resolve eq347 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq444 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X0))) = X0 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq410 X0 X2
       grind)
    | exact superpose eq410 eq9
    | (have j1 := eq410 X0 X2
       grind)
    | exact resolve eq9 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq569 : ∀ X0 X2 : G, (M.op X0 X0) = X0 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq9 X0 X0 x
       have i₂ := eq444 X0 x X2
       grind)
    | exact superpose eq444 eq9
    | (have j1 := eq444 X0 x X2
       grind)
    | exact resolve eq9 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq574 : ∀ X0 X2 : G, (M.op X2 X0) = (k X2 X0) := by
    intro X0 X2
    first
    | (have j0 := eq569 X0 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq569 x X2
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq569 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq618 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq574 (σ X1) (σ X0)
       grind)
    | exact superpose eq574 eq15
    | exact resolve eq15 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq645 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq618 X0 X1
       have i₂ := eq574 X1 X0
       grind)
    | exact superpose eq574 eq618
    | exact resolve eq618 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574 eq618
  have eq970 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq645 x y
       grind)
    | exact superpose eq645 eq16
    | (have r₁ := eq16
       have r₂ := eq645 x y
       grind)
    | exact resolve eq16 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq987 : False := by grind
  exact eq987

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_x_pxy_Equation422 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law422 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq267 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq267 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq270 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq268 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq268 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq268 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq281 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq270 (σ X0)
       grind)
    | exact superpose eq270 eq15
    | exact resolve eq15 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq281 X0
       have i₂ := eq270 X0
       grind)
    | exact superpose eq270 eq281
    | exact resolve eq281 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270 eq281
  have eq345 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq300 X0
       grind)
    | exact superpose eq300 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq300 X0
       grind)
    | exact superpose eq300 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq347 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq345 X0 X1
       have j1 := eq346 X0 X1
       grind)
    | (have r₁ := eq345 X0 X1
       have r₂ := eq346 X0 X1
       grind)
    | exact resolve eq345 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345 eq346
  have eq410 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq347 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq347
    | exact resolve eq347 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq443 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X0))) = X0 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq410 X0 X2
       grind)
    | exact superpose eq410 eq9
    | (have j1 := eq410 X0 X2
       grind)
    | exact resolve eq9 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq971 : ∀ X0 X2 : G, (M.op X0 X0) = X0 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq9 X0 X0 x
       have i₂ := eq443 X0 x X2
       grind)
    | exact superpose eq443 eq9
    | (have j1 := eq443 X0 x X2
       grind)
    | exact resolve eq9 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq986 : ∀ X0 X2 : G, (M.op X2 X0) = (k X2 X0) := by
    intro X0 X2
    first
    | (have j0 := eq971 X0 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq971 x X2
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq971 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971
  have eq1023 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq986 (σ X1) (σ X0)
       grind)
    | exact superpose eq986 eq15
    | exact resolve eq15 eq986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1041 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1023 X0 X1
       have i₂ := eq986 X1 X0
       grind)
    | exact superpose eq986 eq1023
    | exact resolve eq1023 eq986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986 eq1023
  have eq1364 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1041 x y
       grind)
    | exact superpose eq1041 eq16
    | (have r₁ := eq16
       have r₂ := eq1041 x y
       grind)
    | exact resolve eq16 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041
  have eq1387 : False := by grind
  exact eq1387

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation422 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law422 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq66 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq76 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq67 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq77 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq76 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq92 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq77 (σ X0)
       grind)
    | exact superpose eq77 eq15
    | exact resolve eq15 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq92 X0
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq92
    | exact resolve eq92 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq92
  have eq120 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq103 X0
       grind)
    | exact superpose eq103 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq103 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq103
    | (have j1 := eq14 (σ X0) (σ (M.op X0 X0))
       grind)
    | exact resolve eq103 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq134 X0 X1
       have j1 := eq120 X0 X1
       grind)
    | (have r₁ := eq134 X0 X1
       have r₂ := eq120 X0 X1
       grind)
    | (have r₁ := eq134 X0 (σ (M.op X0 X0))
       have r₂ := eq120 X0 X1
       grind)
    | (have r₁ := eq134 (M.op X0 X0) (σ X0)
       have r₂ := eq120 X0 X1
       grind)
    | exact resolve eq134 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq134
  have eq166 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq144 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq144
    | exact resolve eq144 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq144 X1 (σ X0)
       grind)
    | exact superpose eq144 eq15
    | (have j1 := eq144 (k X0 X1) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq178 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq166 (τ X1) X0
       grind)
    | exact superpose eq166 eq19
    | (have j1 := eq166 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq166
  have eq262 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq178 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq178
    | exact resolve eq178 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq285 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq262 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq262
    | (have j0 := eq262 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq262 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq895 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq171 x y
       grind)
    | exact superpose eq171 eq16
    | (have j1 := eq171 x y
       grind)
    | exact resolve eq16 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq909 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq895
       have i₂ := eq285 y x
       grind)
    | exact superpose eq285 eq895
    | (have j1 := eq285 (σ x) (σ y)
       grind)
    | (have r₁ := eq895
       have r₂ := eq285 y x
       grind)
    | (have r₁ := eq895
       have r₂ := eq285 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq895
       have r₂ := eq285 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq895 eq285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285 eq895
  have eq910 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq909
  have eq912 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq910
       grind)
    | exact superpose eq910 eq16
    | exact resolve eq16 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq913 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq912
       have r₂ := eq103 x
       grind)
    | exact resolve eq912 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq914 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq913
       grind)
    | exact superpose eq913 eq16
    | exact resolve eq16 eq913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq915 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq913
       grind)
    | exact superpose eq913 eq10
    | exact resolve eq10 eq913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913
  have eq957 : x = y := by
    first
    | (have i₁ := eq915
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq915
    | exact resolve eq915 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915
  have eq958 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq914
       have i₂ := eq103 x
       grind)
    | exact superpose eq103 eq914
    | exact resolve eq914 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq914
  have eq959 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq958
       have i₂ := eq957
       grind)
    | exact superpose eq957 eq958
    | exact resolve eq958 eq957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957 eq958
  have eq960 : False := by grind
  exact eq960

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyy_pxy_Equation422 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law422 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq373 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq390 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq407 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq390 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq390
    | (have j0 := eq390 X0 X1
       grind)
    | exact resolve eq390 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq2832 : ∀ X0 X1 : G, (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (M.op (σ X1) (σ X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq407 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq407
    | (have j0 := eq407 (σ X0) (σ X1)
       grind)
    | exact resolve eq407 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq2939 : ∀ X0 X1 : G, (σ (σ (M.op X1 X1))) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2832 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq2832
    | (have j0 := eq2832 X0 X1
       grind)
    | exact resolve eq2832 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2832
  have eq3010 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) ≠ (M.op X1 (σ (σ X0))) ∨ (σ (σ X0)) = X1 ∨ (σ (σ (M.op X0 X0))) = (k X1 (σ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq373 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq373
    | (have j0 := eq373 (σ X0) X1
       grind)
    | (have r₁ := eq373 X0 (σ X0)
       have r₂ := eq22 X0
       grind)
    | exact resolve eq373 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq70309 : ∀ X0 X1 : G, (σ (σ (M.op X1 X1))) = (M.op (σ X0) (σ (σ X1))) ∨ (σ (σ (k (τ X0) X1))) = (M.op (σ X0) (σ (σ X1))) ∨ (σ X0) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2939 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2939
    | exact resolve eq2939 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2939
  have eq70709 : ∀ X0 X1 : G, (σ (k X0 (σ X1))) = (M.op (σ X0) (σ (σ X1))) ∨ (σ (σ (M.op X1 X1))) = (M.op (σ X0) (σ (σ X1))) ∨ (σ X0) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq70309 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq70309
    | (have j0 := eq70309 X0 X1
       grind)
    | exact resolve eq70309 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70309
  have eq70899 : ∀ X0 X1 : G, (k X0 (σ (σ X1))) = (M.op (σ (τ X0)) (σ (σ X1))) ∨ (σ (σ (M.op X1 X1))) = (M.op (σ (τ X0)) (σ (σ X1))) ∨ (σ (τ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (σ X1)
       have i₂ := eq70709 (τ X0) X1
       grind)
    | exact superpose eq70709 eq18
    | (have j1 := eq70709 (τ X0) X1
       grind)
    | exact resolve eq18 eq70709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq70709
  have eq71056 : ∀ X0 X1 : G, (M.op X0 (σ (σ X1))) = (k X0 (σ (σ X1))) ∨ (σ (σ (M.op X1 X1))) = (M.op (σ (τ X0)) (σ (σ X1))) ∨ (σ (τ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq70899 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq70899
    | (have j0 := eq70899 X0 X1
       grind)
    | exact resolve eq70899 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70899
  have eq71117 : ∀ X0 X1 : G, (σ (σ (M.op X1 X1))) = (M.op X0 (σ (σ X1))) ∨ (M.op X0 (σ (σ X1))) = (k X0 (σ (σ X1))) ∨ (σ (τ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq71056 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq71056
    | (have j0 := eq71056 X0 X1
       grind)
    | exact resolve eq71056 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71056
  have eq71170 : ∀ X0 X1 : G, (σ (σ (M.op X1 X1))) = (M.op X0 (σ (σ X1))) ∨ (σ (σ X1)) = X0 ∨ (M.op X0 (σ (σ X1))) = (k X0 (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq71117 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq71117
    | (have j0 := eq71117 X0 X1
       grind)
    | exact resolve eq71117 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71117
  have eq71566 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) ≠ (σ (σ (M.op X0 X0))) ∨ (σ (σ X0)) = X1 ∨ (σ (σ (M.op X0 X0))) = (k X1 (σ (σ X0))) ∨ (σ (σ X0)) = X1 ∨ (M.op X1 (σ (σ X0))) = (k X1 (σ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3010 X0 X1
       have i₂ := eq71170 X1 X0
       grind)
    | exact superpose eq71170 eq3010
    | (have j0 := eq3010 X0 X1
       have j1 := eq71170 X1 X0
       grind)
    | (have r₁ := eq3010 X1 X0
       have r₂ := eq71170 X0 X1
       grind)
    | (have r₁ := eq3010 X0 X1
       have r₂ := eq71170 (M.op X1 (σ (σ X0))) (M.op X0 X0)
       grind)
    | exact resolve eq3010 eq71170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3010
  have eq71612 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) ≠ (σ (σ (M.op X0 X0))) ∨ (σ (σ X0)) = X1 ∨ (σ (σ (M.op X0 X0))) = (k X1 (σ (σ X0))) ∨ (M.op X1 (σ (σ X0))) = (k X1 (σ (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq71566 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71566
  have eq71613 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) = (k X1 (σ (σ X0))) ∨ (σ (σ X0)) = X1 ∨ (M.op X1 (σ (σ X0))) = (k X1 (σ (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq71612 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71612
  have eq126425 : ∀ X0 X1 : G, (σ (σ (M.op X1 X1))) ≠ (M.op X0 (σ (σ X1))) ∨ (σ (σ X1)) = X0 ∨ (M.op X0 (σ (σ X1))) = (k X0 (σ (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq71613 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71613
  have eq126433 : ∀ X0 X1 : G, (M.op X0 (σ (σ X1))) = (k X0 (σ (σ X1))) ∨ (σ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq126425 X0 X1
       have j1 := eq71170 X0 X1
       grind)
    | (have r₁ := eq126425 X0 X1
       have r₂ := eq71170 X0 X1
       grind)
    | (have r₁ := eq126425 X0 X1
       have r₂ := eq71170 (M.op X0 (σ (σ X1))) (M.op X1 X1)
       grind)
    | exact resolve eq126425 eq71170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71170 eq126425
  have eq126896 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq126433 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq126433
    | exact resolve eq126433 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126433
  have eq127442 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq126896 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq126896
    | exact resolve eq126896 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127537 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq126896 X1 (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq126896
    | (have j0 := eq126896 (k X0 X1) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq126896 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126896
  have eq130111 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq127537 X0 X1
       have i₂ := eq127442 X1 X0
       grind)
    | exact superpose eq127442 eq127537
    | (have j0 := eq127537 X0 X1
       have j1 := eq127442 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq127537 eq127442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127442 eq127537
  have eq133450 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq130111 x y
       grind)
    | exact superpose eq130111 eq16
    | (have j1 := eq130111 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq130111 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq130111 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq130111 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq130111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130111
  have eq133504 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq133450
  have eq133535 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq133504
       grind)
    | exact superpose eq133504 eq10
    | exact resolve eq10 eq133504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133504
  have eq133718 : x = y ∨ x = y := by
    first
    | (have i₁ := eq133535
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq133535
    | exact resolve eq133535 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133535
  have eq133719 : x = y := by grind
  clear eq133718
  have eq133722 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq133719
       grind)
    | exact superpose eq133719 eq16
    | exact resolve eq16 eq133719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133719
  have eq133723 : False := by grind
  exact eq133723

/-- `Equation426`: `x = x ◇ (y ◇ (x ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pxy_pyx_pxy_Equation426 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law426 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law426.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq373 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq595 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq373 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq373 X0 X1
       grind)
    | exact superpose eq373 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq373 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq373 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq373 X0 X1
       grind)
    | exact resolve eq13 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq598 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq595 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq599 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq598 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq604 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq599 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq599
    | (have j0 := eq599 X0 X1
       grind)
    | exact resolve eq599 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq605 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq604 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq621 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq605 (τ X0) (τ X1)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq605
    | (have j0 := eq605 (τ X0) (τ X1)
       grind)
    | exact resolve eq605 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq666 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq621 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq621
    | (have j0 := eq621 X0 X1
       grind)
    | exact resolve eq621 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq683 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq666 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq666
    | (have j0 := eq666 X0 X1
       grind)
    | exact resolve eq666 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq688 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq683 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq683
    | (have j0 := eq683 X0 X1
       grind)
    | exact resolve eq683 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq693 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq688 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq688
    | (have j0 := eq688 X0 X1
       grind)
    | exact resolve eq688 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq698 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq693 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq693
    | (have j0 := eq693 X0 X1
       grind)
    | exact resolve eq693 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq709 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq605 X0 X1
       have i₂ := eq698 X0 X1
       grind)
    | exact superpose eq698 eq605
    | (have j0 := eq605 X0 X1
       have j1 := eq698 (σ X0) (σ X1)
       grind)
    | exact resolve eq605 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6904 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq709 x y
       grind)
    | exact superpose eq709 eq16
    | (have j1 := eq709 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq709 x y
       grind)
    | exact resolve eq16 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq6928 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq6904
  have eq6962 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq6928
  have eq6970 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq6962
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq6962
    | exact resolve eq6962 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6962
  have eq6981 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq698 eq6970
    | (have j1 := eq698 x y
       grind)
    | exact resolve eq6970 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698 eq6970
  have eq6986 : x = (M.op y y) := by
    first
    | (have r₁ := eq6981
       have r₂ := eq16
       grind)
    | exact resolve eq6981 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6981
  have eq6991 : (M.op x y) = (k x y) := by grind
  clear eq6986
  have eq6997 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq605 x y
       have i₂ := eq6991
       grind)
    | exact superpose eq6991 eq605
    | (have j0 := eq605 x y
       grind)
    | exact resolve eq605 eq6991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq6998 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq6997
       have r₂ := eq16
       grind)
    | exact resolve eq6997 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6997
  have eq7025 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq6998
  have eq7033 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq7025
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq7025
    | exact resolve eq7025 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7025
  have eq7043 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7033
       have i₂ := eq6991
       grind)
    | exact superpose eq6991 eq7033
    | exact resolve eq7033 eq6991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6991 eq7033
  have eq7048 : False := by grind
  exact eq7048

/-- `Equation426`: `x = x ◇ (y ◇ (x ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pyy_pxy_Equation426 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law426 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law426.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq19 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq19 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq19 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
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
  have eq30 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq34 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq35 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq31 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq31 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq33 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq33 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq34 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq34 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq35 X1 X0
       grind)
    | (have r₁ := eq37 X1 X0
       have r₂ := eq35 X0 X1
       grind)
    | exact resolve eq37 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq37
  have eq45 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 X1
       have i₂ := eq20 X1
       grind)
    | exact superpose eq20 eq42
    | (have j0 := eq42 X0 X1
       grind)
    | exact resolve eq42 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq42
  have eq92 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq36 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq96 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq92 X0 X1
       have j1 := eq45 X0 X1
       grind)
    | (have r₁ := eq92 X0 X1
       have r₂ := eq45 X0 X1
       grind)
    | (have r₁ := eq92 X1 X1
       have r₂ := eq45 X1 X1
       grind)
    | exact resolve eq92 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq92
  have eq211 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq96 (σ X0) (σ X1)
       grind)
    | exact superpose eq96 eq15
    | exact resolve eq15 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq211 X0 X1
       have i₂ := eq96 X0 X1
       grind)
    | exact superpose eq96 eq211
    | exact resolve eq211 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq211
  have eq221 : False := by grind
  exact eq221
