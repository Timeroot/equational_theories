import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1496`: `x = (y ◇ x) ◇ (y ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_y_pxy_Equation1496 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1496 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1496.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
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
  clear eq35
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
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, y = (M.op (M.op x y) (M.op x (M.op X0 X0))) := by
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
  have eq179 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X1) X0) X2) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op (M.op X1 X1) X0) (M.op X1 X1)
       have i₂ := eq16 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (k X1 X1) X0) X2) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179 X0 X1 X2
       have i₂ := eq174 X1
       grind)
    | exact superpose eq174 eq179
    | exact resolve eq179 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq183 : ∀ X0 : G, y = (M.op (M.op x y) (M.op x (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq175
    | exact resolve eq175 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq187 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 (k X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq323 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq380 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq445 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq323 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq323
    | exact resolve eq323 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq583 : ∀ X0 : G, y = (M.op (M.op x y) (M.op x (τ (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq183 (τ X0)
       have i₂ := eq445 X0 X0
       grind)
    | exact superpose eq445 eq183
    | exact resolve eq183 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq646 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (k X1 X1) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq180 X0 X1 (M.op (k X1 X1) (M.op X2 X2))
       have i₂ := eq16 X0 (k X1 X1) X2
       grind)
    | exact superpose eq16 eq180
    | exact resolve eq180 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq652 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (k X1 X1) (k X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq646 X0 X1 X2
       have i₂ := eq174 X2
       grind)
    | exact superpose eq174 eq646
    | exact resolve eq646 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq666 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 (τ (k X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq187 (τ X0) X1 X2
       have i₂ := eq445 X0 X0
       grind)
    | exact superpose eq445 eq187
    | exact resolve eq187 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq698 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq652 X0 x x
       have i₂ := eq652 X1 x x
       grind)
    | (have i₁ := eq652 X0 X1 X1
       have i₂ := eq652 (k X1 X1) X1 x
       grind)
    | exact superpose eq652 eq652
    | exact resolve eq652 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq714 : ∀ X0 X1 X2 : G, (M.op (M.op (k X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq187 x (k X1 X1) X2
       have i₂ := eq652 X0 X1 x
       grind)
    | (have i₁ := eq187 X0 (k X0 X0) X2
       have i₂ := eq652 (k X0 X0) X1 X2
       grind)
    | exact superpose eq652 eq187
    | exact resolve eq187 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq721 : ∀ X0 X1 X2 : G, (M.op (M.op (k X1 X1) X2) (k X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq714 X0 X1 X2
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq714
    | exact resolve eq714 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq757 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (k X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq187 X2 X1 X1
       have i₂ := eq698 X1 X0
       grind)
    | (have i₁ := eq187 X2 X1 X1
       have i₂ := eq698 X0 X1
       grind)
    | exact superpose eq698 eq187
    | exact resolve eq187 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq763 : ∀ X0 X2 : G, (M.op X0 X0) = (k X2 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq187 X2 x (k X2 X2)
       have i₂ := eq698 (M.op x (k X2 X2)) X0
       grind)
    | (have i₁ := eq187 X2 x (k X2 X2)
       have i₂ := eq698 X0 (M.op x (k X2 X2))
       grind)
    | exact superpose eq698 eq187
    | exact resolve eq187 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq773 : ∀ X0 X1 X2 : G, (M.op (k X0 X0) (M.op X1 (k X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq757 X0 X1 X2
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq757
    | exact resolve eq757 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq807 : ∀ X0 X2 : G, (k X0 X0) = (k X2 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq187 X2 x (k X2 X2)
       have i₂ := eq763 (M.op x (k X2 X2)) X0
       grind)
    | exact superpose eq763 eq187
    | exact resolve eq187 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq825 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq763 X0 (σ X1)
       grind)
    | exact superpose eq763 eq10
    | exact resolve eq10 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq826 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq380 X1 (σ X1)
       have i₂ := eq763 X0 (σ X1)
       grind)
    | exact superpose eq763 eq380
    | exact resolve eq380 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq827 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq445 X1 X1
       have i₂ := eq763 X0 (τ X1)
       grind)
    | exact superpose eq763 eq445
    | exact resolve eq445 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq828 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 (τ X1)
       have i₂ := eq763 X0 (τ X1)
       grind)
    | exact superpose eq763 eq34
    | exact resolve eq34 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq763
  have eq829 : ∀ X0 X1 : G, (k X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq828 X0 X1
       have i₂ := eq14 X1
       grind)
    | exact superpose eq14 eq828
    | exact resolve eq828 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq830 : ∀ X0 X1 : G, (k X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq826 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq826
    | exact resolve eq826 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq846 : ∀ X0 X1 : G, (k X1 X1) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq829 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq829
    | exact resolve eq829 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq847 : ∀ X0 X1 : G, (k X1 X1) = (τ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq830 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq830
    | exact resolve eq830 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830
  have eq996 : ∀ X0 X1 X2 : G, (M.op (k X1 X1) X2) = (M.op (σ (k X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq180 X2 X1 (M.op (k X1 X1) X2)
       have i₂ := eq825 (M.op (k X1 X1) X2) X0
       grind)
    | exact superpose eq825 eq180
    | exact resolve eq180 eq825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq1012 : ∀ X0 X1 : G, (k x (k X1 X1)) = (τ (k (σ x) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq44 (k X1 X1)
       have i₂ := eq825 X0 X1
       grind)
    | exact superpose eq825 eq44
    | exact resolve eq44 eq825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq1027 : ∀ X0 X1 : G, (k x (k X1 X1)) = (k x (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | exact superpose eq90 eq1012
    | exact resolve eq1012 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq1012
  have eq1058 : ∀ X0 X1 : G, (k x (k X1 X1)) = (k x (τ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1027 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq1027
    | exact resolve eq1027 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027
  have eq1065 : ∀ X0 X2 : G, (τ (k X0 X0)) = (τ (k X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq827 x X2
       have i₂ := eq827 x X0
       grind)
    | exact superpose eq827 eq827
    | exact resolve eq827 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1092 : ∀ X0 X2 : G, (τ (k X0 X0)) = (σ (k X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq825 x X2
       have i₂ := eq827 x X0
       grind)
    | exact superpose eq827 eq825
    | exact resolve eq825 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825 eq827
  have eq1156 : ∀ X0 X1 : G, (k X1 X1) = (σ (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq846 x X1
       have i₂ := eq846 X0 x
       grind)
    | exact superpose eq846 eq846
    | exact resolve eq846 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1258 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1259 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq1258 X0
       have j1 := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq1258 x
       have r₂ := eq13 (M.op x x) x
       grind)
    | (have r₁ := eq1258 X0
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq1258 X0
       have r₂ := eq13 (M.op X0 X0) (k X0 (M.op X0 X0))
       grind)
    | exact resolve eq1258 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1258
  have eq1264 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1259 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq1259
    | exact resolve eq1259 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1259
  have eq1293 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ x = y := by
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
  have eq1300 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
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
  have eq1308 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1300
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq1300
    | exact resolve eq1300 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1300
  have eq1312 : (M.op x y) = (k x y) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq1293
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq1293
    | exact resolve eq1293 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293
  have eq1349 : ∀ X0 X1 : G, (k X1 X1) = (τ (τ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq847 x X1
       have i₂ := eq847 X0 x
       grind)
    | exact superpose eq847 eq847
    | exact resolve eq847 eq847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1443 : ∀ X0 X1 : G, (σ (k X0 X0)) = (k X1 (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1264 X1
       have i₂ := eq846 X0 X1
       grind)
    | exact superpose eq846 eq1264
    | exact resolve eq1264 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1445 : ∀ X0 X1 : G, (k X0 X0) = (k X1 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1264 X0
       have i₂ := eq807 X0 x
       grind)
    | (have i₁ := eq1264 x
       have i₂ := eq807 X0 x
       grind)
    | exact superpose eq807 eq1264
    | exact resolve eq1264 eq807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264
  have eq1760 : ∀ X0 X1 : G, (τ (τ (k X0 X0))) = (τ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1065 X1 x
       have i₂ := eq847 X0 x
       grind)
    | exact superpose eq847 eq1065
    | exact resolve eq1065 eq847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065
  have eq2089 : ∀ X0 X1 : G, (k X1 X1) = (σ (σ (σ (σ (k X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1156 x X1
       have i₂ := eq1156 X0 x
       grind)
    | exact superpose eq1156 eq1156
    | exact resolve eq1156 eq1156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2138 : ∀ X0 X1 : G, (τ (k X1 X1)) = (σ (σ (σ (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1092 X1 x
       have i₂ := eq1156 X0 x
       grind)
    | exact superpose eq1156 eq1092
    | exact resolve eq1092 eq1156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1156
  have eq4578 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1312
       grind)
    | exact superpose eq1312 eq40
    | exact resolve eq40 eq1312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1312
  have eq4579 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq4578
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4578
    | exact resolve eq4578 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4578
  have eq4581 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k x x) ∨ x = y := by
    first
    | exact superpose eq20 eq4579
    | exact resolve eq4579 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4579
  have eq15399 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y := by
    first
    | exact superpose eq4581 eq1308
    | exact resolve eq1308 eq4581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1308 eq4581
  have eq15406 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq15399
       have r₂ := eq27
       grind)
    | exact resolve eq15399 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15399
  have eq15500 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y := by
    first
    | exact superpose eq15406 eq97
    | exact resolve eq97 eq15406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq15406
  have eq15729 : y = (k x x) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y := by
    first
    | exact superpose eq31 eq15500
    | exact resolve eq15500 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15500
  have eq15730 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq15729
  have eq15829 : ∀ X0 X1 : G, (M.op (M.op y X0) (k X1 X1)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq721 X1 x X0
       have i₂ := eq15730
       grind)
    | exact superpose eq15730 eq721
    | exact resolve eq721 eq15730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq15833 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X1 y)) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq773 X0 X1 x
       have i₂ := eq15730
       grind)
    | exact superpose eq15730 eq773
    | exact resolve eq773 eq15730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq15835 : ∀ X0 : G, y = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq807 X0 x
       have i₂ := eq15730
       grind)
    | exact superpose eq15730 eq807
    | exact resolve eq807 eq15730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15849 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (M.op (σ y) X1) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq996 x X0 X1
       have i₂ := eq15730
       grind)
    | exact superpose eq15730 eq996
    | exact resolve eq996 eq15730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996
  have eq15857 : ∀ X0 : G, (k x (k X0 X0)) = (k x (τ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1058 x X0
       have i₂ := eq15730
       grind)
    | exact superpose eq15730 eq1058
    | exact resolve eq1058 eq15730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058
  have eq15863 : ∀ X0 : G, (σ y) = (τ (k X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1092 X0 x
       have i₂ := eq15730
       grind)
    | exact superpose eq15730 eq1092
    | exact resolve eq1092 eq15730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092
  have eq15875 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1443 x x
       have i₂ := eq15730
       grind)
    | exact superpose eq15730 eq1443
    | exact resolve eq1443 eq15730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1443 eq15730
  have eq15946 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq15875 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15875
    | (have j0 := eq15875 X0
       grind)
    | exact resolve eq15875 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15875
  have eq15955 : ∀ X0 : G, (σ y) = (τ (k X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq15863 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15863
    | (have j0 := eq15863 X0
       grind)
    | exact resolve eq15863 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15863
  have eq15961 : ∀ X0 : G, (k X0 X0) = (k x (τ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq15857 X0
       have i₂ := eq1445 X0 x
       grind)
    | exact superpose eq1445 eq15857
    | exact resolve eq15857 eq1445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445 eq15857
  have eq15969 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (M.op (σ y) X1) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq15849 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15849
    | (have j0 := eq15849 X0 X1
       grind)
    | exact resolve eq15849 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15849
  have eq15982 : ∀ X1 : G, (M.op y (M.op X1 y)) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq15835 eq15833
    | exact resolve eq15833 eq15835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15833
  have eq15984 : ∀ X0 : G, (M.op (M.op y X0) y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq15835 eq15829
    | exact resolve eq15829 eq15835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15829
  have eq16029 : (σ y) = (τ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq15835 eq15955
    | exact resolve eq15955 eq15835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15955
  have eq16032 : y = (k x (τ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq15835 eq15961
    | exact resolve eq15961 eq15835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15961
  have eq16038 : ∀ X1 : G, (M.op (σ y) X1) = (M.op y X1) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq15835 eq15969
    | exact resolve eq15969 eq15835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15969
  have eq16070 : y = (k x (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq16029 eq16032
    | exact resolve eq16032 eq16029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16029 eq16032
  have eq16091 : (σ x) = (σ y) ∨ y = (σ y) ∨ x = y := by
    first
    | exact superpose eq15946 eq16070
    | exact resolve eq16070 eq15946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16070
  have eq16127 : y = (τ (σ x)) ∨ y = (σ y) ∨ x = y := by
    first
    | exact superpose eq16091 eq31
    | exact resolve eq31 eq16091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16152 : x = y ∨ y = (σ y) ∨ x = y := by
    first
    | exact superpose eq29 eq16127
    | exact resolve eq16127 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16127
  have eq16153 : y = (σ y) ∨ x = y := by grind
  clear eq16152
  have eq16155 : (M.op x y) = (M.op x (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq16153
       grind)
    | exact superpose eq16153 eq18
    | exact resolve eq18 eq16153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16157 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (k (σ y) X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq16153
       grind)
    | exact superpose eq16153 eq36
    | exact resolve eq36 eq16153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq16168 : x ≠ (σ y) ∨ x = y := by grind
  have eq19757 : x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq15982 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15982
    | (have j0 := eq15982 x
       grind)
    | exact resolve eq15982 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15982
  have eq19776 : x = (M.op (σ y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq16091 eq19757
    | exact resolve eq19757 eq16091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19757
  have eq19882 : ∀ X0 : G, (M.op (k y X0) y) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op y y) = X0 ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq15984 X0
       have i₂ := eq11 y X0
       grind)
    | exact superpose eq11 eq15984
    | (have j1 := eq11 y X0
       grind)
    | exact resolve eq15984 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15984
  have eq19915 : ∀ X0 : G, (k y y) = X0 ∨ (M.op (k y X0) y) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq19882 X0
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq19882
    | (have j0 := eq19882 X0
       grind)
    | exact resolve eq19882 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19882
  have eq19933 : ∀ X0 : G, y = X0 ∨ (M.op (k y X0) y) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ y = X0 := by
    intro X0
    first
    | exact superpose eq15835 eq19915
    | (have j0 := eq19915 X0
       grind)
    | exact resolve eq19915 eq15835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19915
  have eq19934 : ∀ X0 : G, y = X0 ∨ (M.op (k y X0) y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq19933 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19933
  have eq19952 : ∀ X0 : G, (σ y) = X0 ∨ (M.op (k y X0) y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq16091 eq19934
    | (have j0 := eq19934 x
       grind)
    | exact resolve eq19934 eq16091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19934
  have eq19961 : ∀ X0 : G, (M.op (k (σ y) X0) (σ y)) = X0 ∨ (σ y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq16091 eq19952
    | (have j0 := eq19952 X0
       grind)
    | exact resolve eq19952 eq16091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19952
  have eq22361 : ∀ X0 : G, (k y X0) = (M.op (σ y) X0) ∨ (M.op y y) = X0 ∨ y = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq11 y X0
       have i₂ := eq16038 X0
       grind)
    | exact superpose eq16038 eq11
    | (have j0 := eq11 y X0
       grind)
    | exact resolve eq11 eq16038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16038
  have eq22425 : ∀ X0 : G, (k y y) = X0 ∨ (k y X0) = (M.op (σ y) X0) ∨ y = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq22361 X0
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq22361
    | (have j0 := eq22361 X0
       grind)
    | exact resolve eq22361 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22361
  have eq22471 : ∀ X0 : G, y = X0 ∨ (k y X0) = (M.op (σ y) X0) ∨ y = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq15835 eq22425
    | (have j0 := eq22425 X0
       grind)
    | exact resolve eq22425 eq15835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15835 eq22425
  have eq22472 : ∀ X0 : G, y = X0 ∨ (k y X0) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq22471 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22471
  have eq22509 : ∀ X0 : G, (σ y) = X0 ∨ (k y X0) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq16091 eq22472
    | (have j0 := eq22472 x
       grind)
    | exact resolve eq22472 eq16091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22472
  have eq22537 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) ∨ (σ y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq16091 eq22509
    | (have j0 := eq22509 X0
       grind)
    | exact resolve eq22509 eq16091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22509
  have eq58227 : x = (k (σ y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22537 eq19776
    | (have j1 := eq22537 (σ x)
       grind)
    | exact resolve eq19776 eq22537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22537
  have eq58293 : x = (k (σ y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by grind
  clear eq58227
  have eq58542 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq58293 eq16157
    | exact resolve eq16157 eq58293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16157 eq58293
  have eq58545 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ y) := by grind
  clear eq58542
  have eq58549 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq20 eq58545
    | exact resolve eq58545 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58545
  have eq58551 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq58549
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq58549
    | exact resolve eq58549 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58549
  have eq58554 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq58551 eq19961
    | (have j0 := eq19961 (σ (M.op x y))
       grind)
    | exact resolve eq19961 eq58551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19961 eq58551
  have eq58559 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by grind
  clear eq58554
  have eq58562 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq26 eq58559
    | exact resolve eq58559 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58559
  have eq58566 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | (have r₁ := eq58562
       have r₂ := eq27
       grind)
    | exact resolve eq58562 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58562
  have eq58571 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq58566 eq31
    | exact resolve eq31 eq58566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58566
  have eq58637 : x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq29 eq58571
    | exact resolve eq58571 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58571
  have eq58638 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by grind
  clear eq58637
  have eq58652 : (M.op x y) = (τ (σ y)) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq58638 eq28
    | exact resolve eq28 eq58638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58638
  have eq58676 : (M.op x y) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq58652
    | exact resolve eq58652 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58652
  have eq59149 : y = (τ (M.op x y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq58676 eq31
    | exact resolve eq31 eq58676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59191 : (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq58676 eq16091
    | exact resolve eq16091 eq58676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16091 eq58676
  have eq59252 : (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq59191
  have eq59323 : (σ y) = (τ (M.op x y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq16153 eq59149
    | exact resolve eq59149 eq16153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59149
  have eq59346 : (σ y) = (τ (M.op x y)) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq16153 eq59323
    | exact resolve eq59323 eq16153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59323
  have eq59377 : x = (τ (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq59252 eq29
    | exact resolve eq29 eq59252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59252
  have eq59459 : x = (τ (M.op x y)) ∨ (M.op x y) = (σ y) ∨ x = y := by
    first
    | exact superpose eq16153 eq59377
    | exact resolve eq59377 eq16153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59377
  have eq59487 : x = (σ y) ∨ (M.op x y) = (σ y) ∨ x = y := by
    first
    | exact superpose eq59346 eq59459
    | exact resolve eq59459 eq59346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59346 eq59459
  have eq59500 : (M.op x y) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq59487
       have r₂ := eq16168
       grind)
    | exact resolve eq59487 eq16168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16168 eq59487
  have eq59513 : y = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq59500 eq31
    | exact resolve eq31 eq59500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq59538 : ∀ X0 : G, (M.op x y) = (k X0 (M.op x y)) ∨ (M.op x y) = (σ x) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq59500 eq15946
    | exact resolve eq15946 eq59500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15946
  have eq59556 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq59500 eq16155
    | exact resolve eq16155 eq59500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16155
  have eq59565 : x = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq59500 eq19776
    | exact resolve eq19776 eq59500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19776
  have eq59606 : x = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ x = y := by grind
  clear eq59565
  have eq59615 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y := by grind
  clear eq59556
  have eq59633 : ∀ X0 : G, (M.op x y) = (k X0 (M.op x y)) ∨ (M.op x y) = (σ x) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq59538 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59538
  have eq59643 : x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq59606
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq59606
    | exact resolve eq59606 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59606
  have eq59677 : (σ y) = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq16153 eq59513
    | exact resolve eq59513 eq16153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16153 eq59513
  have eq59678 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq59633 eq59643
    | exact resolve eq59643 eq59633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59633 eq59643
  have eq59703 : (M.op x y) = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq59500 eq59677
    | exact resolve eq59677 eq59500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59500 eq59677
  have eq59821 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op x (τ (k X0 X0)))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq59615 eq666
    | exact resolve eq666 eq59615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666 eq59615
  have eq59833 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq583 eq59821
    | exact resolve eq59821 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583 eq59821
  have eq59930 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq59833
  have eq60305 : x = (τ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq59678 eq29
    | exact resolve eq29 eq59678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq59678
  have eq60388 : x = (τ (M.op x y)) ∨ x = y := by
    first
    | (have r₁ := eq60305
       have r₂ := eq59930
       grind)
    | exact resolve eq60305 eq59930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60305
  have eq60415 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq59703 eq60388
    | exact resolve eq60388 eq59703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59703 eq60388
  have eq60428 : x = y := by
    first
    | (have r₁ := eq60415
       have r₂ := eq59930
       grind)
    | exact resolve eq60415 eq59930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59930 eq60415
  have eq60441 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq60428
       grind)
    | exact superpose eq60428 eq18
    | exact resolve eq18 eq60428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq60442 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq60428
       grind)
    | exact superpose eq60428 eq24
    | exact resolve eq24 eq60428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq60428
  have eq60455 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq60442
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq60442
    | exact resolve eq60442 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq60442
  have eq60456 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq60441
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq60441
    | exact resolve eq60441 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60441
  have eq60460 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq60455 eq26
    | exact resolve eq26 eq60455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq60455
  have eq60514 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq60460
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq60460
    | exact resolve eq60460 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq60460
  have eq60579 : ∀ X0 : G, (M.op x y) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq807 X0 x
       have i₂ := eq60456
       grind)
    | exact superpose eq60456 eq807
    | exact resolve eq807 eq60456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60582 : ∀ X0 : G, (σ (M.op x y)) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq846 x X0
       have i₂ := eq60456
       grind)
    | exact superpose eq60456 eq846
    | exact resolve eq846 eq60456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq60583 : ∀ X0 : G, (k X0 X0) = (τ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq847 x X0
       have i₂ := eq60456
       grind)
    | exact superpose eq60456 eq847
    | exact resolve eq847 eq60456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq60617 : ∀ X0 : G, (k X0 X0) = (τ (τ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1349 x X0
       have i₂ := eq60456
       grind)
    | exact superpose eq60456 eq1349
    | exact resolve eq1349 eq60456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1349
  have eq60632 : ∀ X0 : G, (τ (k X0 X0)) = (τ (τ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1760 x X0
       have i₂ := eq60456
       grind)
    | exact superpose eq60456 eq1760
    | exact resolve eq1760 eq60456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1760
  have eq60641 : ∀ X0 : G, (k X0 X0) = (σ (σ (σ (σ (M.op x y))))) := by
    intro X0
    first
    | (have i₁ := eq2089 x X0
       have i₂ := eq60456
       grind)
    | exact superpose eq60456 eq2089
    | exact resolve eq2089 eq60456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2089
  have eq60645 : ∀ X0 : G, (τ (k X0 X0)) = (σ (σ (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq2138 x X0
       have i₂ := eq60456
       grind)
    | exact superpose eq60456 eq2138
    | exact resolve eq2138 eq60456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2138 eq60456
  have eq60712 : ∀ X0 : G, (τ (k X0 X0)) = (σ (σ (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq20 eq60645
    | (have j0 := eq60645 X0
       grind)
    | exact resolve eq60645 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60645
  have eq60716 : ∀ X0 : G, (k X0 X0) = (σ (σ (σ (σ (M.op x y))))) := by
    intro X0
    first
    | exact superpose eq20 eq60641
    | (have j0 := eq60641 X0
       grind)
    | exact resolve eq60641 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60641
  have eq60760 : (σ (M.op x y)) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq60582 x
       have i₂ := eq60583 x
       grind)
    | exact superpose eq60583 eq60582
    | exact resolve eq60582 eq60583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60582 eq60583
  have eq60806 : (τ (τ (M.op x y))) = (σ (σ (σ (M.op x y)))) := by
    first
    | (have i₁ := eq60712 x
       have i₂ := eq60632 x
       grind)
    | exact superpose eq60632 eq60712
    | exact resolve eq60712 eq60632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60632 eq60712
  have eq60810 : (τ (τ (M.op x y))) = (σ (σ (σ (σ (M.op x y))))) := by
    first
    | (have i₁ := eq60716 x
       have i₂ := eq60617 x
       grind)
    | exact superpose eq60617 eq60716
    | exact resolve eq60716 eq60617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60617 eq60716
  have eq60835 : (σ (M.op x y)) = (τ (M.op x y)) := by
    first
    | exact superpose eq20 eq60760
    | exact resolve eq60760 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq60760
  have eq60862 : (τ (τ (M.op x y))) = (σ (τ (τ (M.op x y)))) := by
    first
    | exact superpose eq60806 eq60810
    | exact resolve eq60810 eq60806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60806 eq60810
  have eq60901 : (τ (M.op x y)) = (τ (τ (M.op x y))) := by
    first
    | (have i₁ := eq60862
       have i₂ := eq14 (τ sF0)
       grind)
    | exact superpose eq14 eq60862
    | exact resolve eq60862 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60862
  have eq60929 : (σ (M.op x y)) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq60835 eq60901
    | exact resolve eq60901 eq60835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60835 eq60901
  have eq60945 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq28 eq60929
    | exact resolve eq60929 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq60929
  have eq61199 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k X0 X0) := by
    intro X0
    first
    | exact superpose eq60514 eq807
    | exact resolve eq807 eq60514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807 eq60514
  have eq61407 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq61199 x
       have i₂ := eq60579 x
       grind)
    | exact superpose eq60579 eq61199
    | exact resolve eq61199 eq60579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60579 eq61199
  have eq61814 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq61407 eq27
    | exact resolve eq27 eq61407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq61407
  have eq61853 : False := by grind
  exact eq61853

/-- `Equation1496`: `x = (y ◇ x) ◇ (y ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxx_y_pyx_Equation1496 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1496 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1496.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
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
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, y = (M.op (M.op x y) (M.op x (M.op X0 X0))) := by
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
  have eq179 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X1) X0) X2) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op (M.op X1 X1) X0) (M.op X1 X1)
       have i₂ := eq16 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (k X1 X1) X0) X2) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179 X0 X1 X2
       have i₂ := eq174 X1
       grind)
    | exact superpose eq174 eq179
    | exact resolve eq179 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq183 : ∀ X0 : G, y = (M.op (M.op x y) (M.op x (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq175
    | exact resolve eq175 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq187 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 (k X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq323 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq445 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq323 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq323
    | exact resolve eq323 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq583 : ∀ X0 : G, y = (M.op (M.op x y) (M.op x (τ (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq183 (τ X0)
       have i₂ := eq445 X0 X0
       grind)
    | exact superpose eq445 eq183
    | exact resolve eq183 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq646 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (k X1 X1) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq180 X0 X1 (M.op (k X1 X1) (M.op X2 X2))
       have i₂ := eq16 X0 (k X1 X1) X2
       grind)
    | exact superpose eq16 eq180
    | exact resolve eq180 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq652 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (k X1 X1) (k X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq646 X0 X1 X2
       have i₂ := eq174 X2
       grind)
    | exact superpose eq174 eq646
    | exact resolve eq646 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq666 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 (τ (k X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq187 (τ X0) X1 X2
       have i₂ := eq445 X0 X0
       grind)
    | exact superpose eq445 eq187
    | exact resolve eq187 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq698 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq652 X0 x x
       have i₂ := eq652 X1 x x
       grind)
    | (have i₁ := eq652 X0 X1 X1
       have i₂ := eq652 (k X1 X1) X1 x
       grind)
    | exact superpose eq652 eq652
    | exact resolve eq652 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq714 : ∀ X0 X1 X2 : G, (M.op (M.op (k X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq187 x (k X1 X1) X2
       have i₂ := eq652 X0 X1 x
       grind)
    | (have i₁ := eq187 X0 (k X0 X0) X2
       have i₂ := eq652 (k X0 X0) X1 X2
       grind)
    | exact superpose eq652 eq187
    | exact resolve eq187 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq721 : ∀ X0 X1 X2 : G, (M.op (M.op (k X1 X1) X2) (k X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq714 X0 X1 X2
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq714
    | exact resolve eq714 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq757 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (k X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq187 X2 X1 X1
       have i₂ := eq698 X1 X0
       grind)
    | (have i₁ := eq187 X2 X1 X1
       have i₂ := eq698 X0 X1
       grind)
    | exact superpose eq698 eq187
    | exact resolve eq187 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq763 : ∀ X0 X2 : G, (M.op X0 X0) = (k X2 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq187 X2 x (k X2 X2)
       have i₂ := eq698 (M.op x (k X2 X2)) X0
       grind)
    | (have i₁ := eq187 X2 x (k X2 X2)
       have i₂ := eq698 X0 (M.op x (k X2 X2))
       grind)
    | exact superpose eq698 eq187
    | exact resolve eq187 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq773 : ∀ X0 X1 X2 : G, (M.op (k X0 X0) (M.op X1 (k X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq757 X0 X1 X2
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq757
    | exact resolve eq757 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq807 : ∀ X0 X2 : G, (k X0 X0) = (k X2 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq187 X2 x (k X2 X2)
       have i₂ := eq763 (M.op x (k X2 X2)) X0
       grind)
    | exact superpose eq763 eq187
    | exact resolve eq187 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq825 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq763 X0 (σ X1)
       grind)
    | exact superpose eq763 eq10
    | exact resolve eq10 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq827 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq445 X1 X1
       have i₂ := eq763 X0 (τ X1)
       grind)
    | exact superpose eq763 eq445
    | exact resolve eq445 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq828 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 (τ X1)
       have i₂ := eq763 X0 (τ X1)
       grind)
    | exact superpose eq763 eq34
    | exact resolve eq34 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq763
  have eq829 : ∀ X0 X1 : G, (k X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq828 X0 X1
       have i₂ := eq14 X1
       grind)
    | exact superpose eq14 eq828
    | exact resolve eq828 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq846 : ∀ X0 X1 : G, (k X1 X1) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq829 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq829
    | exact resolve eq829 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq960 : ∀ X0 X2 : G, (σ (k X0 X0)) = (σ (k X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq825 x X2
       have i₂ := eq825 x X0
       grind)
    | exact superpose eq825 eq825
    | exact resolve eq825 eq825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq969 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq825 X1 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq825
    | exact resolve eq825 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq996 : ∀ X0 X1 X2 : G, (M.op (k X1 X1) X2) = (M.op (σ (k X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq180 X2 X1 (M.op (k X1 X1) X2)
       have i₂ := eq825 (M.op (k X1 X1) X2) X0
       grind)
    | exact superpose eq825 eq180
    | exact resolve eq180 eq825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq825
  have eq1156 : ∀ X0 X1 : G, (k X1 X1) = (σ (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq846 x X1
       have i₂ := eq846 X0 x
       grind)
    | exact superpose eq846 eq846
    | exact resolve eq846 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq1293 : (M.op x y) = (k y x) ∨ y = (M.op x x) ∨ x = y := by
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
  have eq1300 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
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
  have eq1308 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1300
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq1300
    | exact resolve eq1300 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1300
  have eq1312 : (M.op x y) = (k y x) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq1293
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq1293
    | exact resolve eq1293 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293
  have eq1623 : ∀ X0 X2 : G, (σ (σ (k X0 X0))) = (τ (k X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq827 x X2
       have i₂ := eq969 X0 x
       grind)
    | exact superpose eq969 eq827
    | exact resolve eq827 eq969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827 eq969
  have eq2048 : ∀ X0 X1 : G, (σ (k X1 X1)) = (σ (σ (σ (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq960 X1 x
       have i₂ := eq1156 X0 x
       grind)
    | exact superpose eq1156 eq960
    | exact resolve eq960 eq1156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960 eq1156
  have eq7816 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1312
       grind)
    | exact superpose eq1312 eq39
    | exact resolve eq39 eq1312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1312
  have eq7817 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq7816
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7816
    | exact resolve eq7816 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7816
  have eq7819 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k x x) ∨ x = y := by
    first
    | exact superpose eq20 eq7817
    | exact resolve eq7817 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7817
  have eq12450 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y := by
    first
    | exact superpose eq7819 eq1308
    | exact resolve eq1308 eq7819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1308 eq7819
  have eq12457 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq12450
       have r₂ := eq27
       grind)
    | exact resolve eq12450 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12450
  have eq12464 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y := by
    first
    | exact superpose eq12457 eq97
    | exact resolve eq97 eq12457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq12457
  have eq12687 : y = (k x x) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y := by
    first
    | exact superpose eq31 eq12464
    | exact resolve eq12464 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12464
  have eq12688 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq12687
  have eq12783 : ∀ X0 X1 : G, (M.op (M.op y X0) (k X1 X1)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq721 X1 x X0
       have i₂ := eq12688
       grind)
    | exact superpose eq12688 eq721
    | exact resolve eq721 eq12688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq12787 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X1 y)) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq773 X0 X1 x
       have i₂ := eq12688
       grind)
    | exact superpose eq12688 eq773
    | exact resolve eq773 eq12688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq12789 : ∀ X0 : G, y = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq807 X0 x
       have i₂ := eq12688
       grind)
    | exact superpose eq12688 eq807
    | exact resolve eq807 eq12688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq12803 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (M.op (σ y) X1) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq996 x X0 X1
       have i₂ := eq12688
       grind)
    | exact superpose eq12688 eq996
    | exact resolve eq996 eq12688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996
  have eq12844 : ∀ X0 : G, (τ (k X0 X0)) = (σ (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1623 x X0
       have i₂ := eq12688
       grind)
    | exact superpose eq12688 eq1623
    | exact resolve eq1623 eq12688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1623
  have eq12853 : ∀ X0 : G, (σ (k X0 X0)) = (σ (σ (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2048 x X0
       have i₂ := eq12688
       grind)
    | exact superpose eq12688 eq2048
    | exact resolve eq2048 eq12688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2048 eq12688
  have eq12887 : ∀ X0 : G, (σ (k X0 X0)) = (σ (σ (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq12853 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12853
    | (have j0 := eq12853 X0
       grind)
    | exact resolve eq12853 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12853
  have eq12894 : ∀ X0 : G, (τ (k X0 X0)) = (σ (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq12844 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12844
    | (have j0 := eq12844 X0
       grind)
    | exact resolve eq12844 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12844
  have eq12921 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (M.op (σ y) X1) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq12803 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12803
    | (have j0 := eq12803 X0 X1
       grind)
    | exact resolve eq12803 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12803
  have eq12934 : ∀ X1 : G, (M.op y (M.op X1 y)) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq12789 eq12787
    | exact resolve eq12787 eq12789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12787
  have eq12936 : ∀ X0 : G, (M.op (M.op y X0) y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq12789 eq12783
    | exact resolve eq12783 eq12789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12783
  have eq12971 : (σ y) = (σ (σ (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12789 eq12887
    | exact resolve eq12887 eq12789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12887
  have eq12975 : (σ (σ y)) = (τ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12789 eq12894
    | exact resolve eq12894 eq12789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12894
  have eq12987 : ∀ X1 : G, (M.op (σ y) X1) = (M.op y X1) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq12789 eq12921
    | exact resolve eq12921 eq12789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12921
  have eq13013 : (σ y) = (σ (σ (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12971
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12971
    | exact resolve eq12971 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12971
  have eq13033 : (σ y) = (σ (τ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12975 eq13013
    | exact resolve eq13013 eq12975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12975 eq13013
  have eq13044 : (σ x) = (σ y) ∨ y = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13033
       have i₂ := eq14 y
       grind)
    | exact superpose eq14 eq13033
    | exact resolve eq13033 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13033
  have eq13060 : y = (τ (σ x)) ∨ y = (σ y) ∨ x = y := by
    first
    | exact superpose eq13044 eq31
    | exact resolve eq31 eq13044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13087 : x = y ∨ y = (σ y) ∨ x = y := by
    first
    | exact superpose eq29 eq13060
    | exact resolve eq13060 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13060
  have eq13088 : y = (σ y) ∨ x = y := by grind
  clear eq13087
  have eq13090 : (M.op x y) = (M.op x (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq13088
       grind)
    | exact superpose eq13088 eq18
    | exact resolve eq18 eq13088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13093 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (σ y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq13088
       grind)
    | exact superpose eq13088 eq40
    | exact resolve eq40 eq13088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq13101 : x ≠ (σ y) ∨ x = y := by grind
  have eq15849 : x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12934 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12934
    | (have j0 := eq12934 x
       grind)
    | exact resolve eq12934 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12934
  have eq15868 : x = (M.op (σ y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq13044 eq15849
    | exact resolve eq15849 eq13044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15849
  have eq15975 : ∀ X0 : G, (M.op (k X0 y) y) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op y y) = X0 ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq12936 X0
       have i₂ := eq11 X0 y
       grind)
    | exact superpose eq11 eq12936
    | (have j1 := eq11 X0 y
       grind)
    | exact resolve eq12936 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12936
  have eq16009 : ∀ X0 : G, (k y y) = X0 ∨ (M.op (k X0 y) y) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq15975 X0
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq15975
    | (have j0 := eq15975 X0
       grind)
    | exact resolve eq15975 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15975
  have eq16028 : ∀ X0 : G, y = X0 ∨ (M.op (k X0 y) y) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ y = X0 := by
    intro X0
    first
    | exact superpose eq12789 eq16009
    | (have j0 := eq16009 X0
       grind)
    | exact resolve eq16009 eq12789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16009
  have eq16029 : ∀ X0 : G, y = X0 ∨ (M.op (k X0 y) y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq16028 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16028
  have eq16047 : ∀ X0 : G, (σ y) = X0 ∨ (M.op (k X0 y) y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq13044 eq16029
    | (have j0 := eq16029 x
       grind)
    | exact resolve eq16029 eq13044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16029
  have eq16056 : ∀ X0 : G, (M.op (k X0 (σ y)) (σ y)) = X0 ∨ (σ y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq13044 eq16047
    | (have j0 := eq16047 X0
       grind)
    | exact resolve eq16047 eq13044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16047
  have eq17739 : ∀ X0 : G, (k X0 y) = (M.op (σ y) X0) ∨ (M.op y y) = X0 ∨ y = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq11 X0 y
       have i₂ := eq12987 X0
       grind)
    | exact superpose eq12987 eq11
    | (have j0 := eq11 X0 y
       grind)
    | exact resolve eq11 eq12987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12987
  have eq17805 : ∀ X0 : G, (k y y) = X0 ∨ (k X0 y) = (M.op (σ y) X0) ∨ y = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq17739 X0
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq17739
    | (have j0 := eq17739 X0
       grind)
    | exact resolve eq17739 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17739
  have eq17850 : ∀ X0 : G, y = X0 ∨ (k X0 y) = (M.op (σ y) X0) ∨ y = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq12789 eq17805
    | (have j0 := eq17805 X0
       grind)
    | exact resolve eq17805 eq12789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17805
  have eq17851 : ∀ X0 : G, y = X0 ∨ (k X0 y) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq17850 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17850
  have eq17885 : ∀ X0 : G, (σ y) = X0 ∨ (k X0 y) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq13044 eq17851
    | (have j0 := eq17851 x
       grind)
    | exact resolve eq17851 eq13044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17851
  have eq17910 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq13044 eq17885
    | (have j0 := eq17885 X0
       grind)
    | exact resolve eq17885 eq13044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17885
  have eq50022 : x = (k (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq17910 eq15868
    | (have j1 := eq17910 (σ x)
       grind)
    | exact resolve eq15868 eq17910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17910
  have eq50088 : x = (k (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by grind
  clear eq50022
  have eq50314 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq50088 eq13093
    | exact resolve eq13093 eq50088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13093 eq50088
  have eq50316 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ y) := by grind
  clear eq50314
  have eq50319 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq20 eq50316
    | exact resolve eq50316 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50316
  have eq50321 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq50319
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq50319
    | exact resolve eq50319 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50319
  have eq50326 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq50321 eq16056
    | (have j0 := eq16056 (σ (M.op x y))
       grind)
    | exact resolve eq16056 eq50321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16056 eq50321
  have eq50330 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by grind
  clear eq50326
  have eq50332 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq26 eq50330
    | exact resolve eq50330 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50330
  have eq50336 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | (have r₁ := eq50332
       have r₂ := eq27
       grind)
    | exact resolve eq50332 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50332
  have eq50342 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq50336 eq31
    | exact resolve eq31 eq50336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50336
  have eq50422 : x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq29 eq50342
    | exact resolve eq50342 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50342
  have eq50423 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by grind
  clear eq50422
  have eq50440 : (M.op x y) = (τ (σ y)) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq50423 eq28
    | exact resolve eq28 eq50423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq50423
  have eq50471 : (M.op x y) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq50440
    | exact resolve eq50440 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50440
  have eq50487 : y = (τ (M.op x y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq50471 eq31
    | exact resolve eq31 eq50471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50528 : (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq50471 eq13044
    | exact resolve eq13044 eq50471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13044 eq50471
  have eq50625 : (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq50528
  have eq50711 : (σ y) = (τ (M.op x y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq13088 eq50487
    | exact resolve eq50487 eq13088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50487
  have eq50740 : (σ y) = (τ (M.op x y)) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq13088 eq50711
    | exact resolve eq50711 eq13088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50711
  have eq50776 : x = (τ (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq50625 eq29
    | exact resolve eq29 eq50625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50625
  have eq50892 : x = (τ (M.op x y)) ∨ (M.op x y) = (σ y) ∨ x = y := by
    first
    | exact superpose eq13088 eq50776
    | exact resolve eq50776 eq13088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50776
  have eq50926 : x = (σ y) ∨ (M.op x y) = (σ y) ∨ x = y := by
    first
    | exact superpose eq50740 eq50892
    | exact resolve eq50892 eq50740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50740 eq50892
  have eq50943 : (M.op x y) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq50926
       have r₂ := eq13101
       grind)
    | exact resolve eq50926 eq13101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13101 eq50926
  have eq50961 : y = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq50943 eq31
    | exact resolve eq31 eq50943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq51003 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq50943 eq13090
    | exact resolve eq13090 eq50943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13090
  have eq51017 : x = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq50943 eq15868
    | exact resolve eq15868 eq50943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15868
  have eq51084 : x = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ x = y := by grind
  clear eq51017
  have eq51098 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y := by grind
  clear eq51003
  have eq51126 : x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq51084
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq51084
    | exact resolve eq51084 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51084
  have eq51160 : (σ y) = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq13088 eq50961
    | exact resolve eq50961 eq13088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13088 eq50961
  have eq51185 : (M.op x y) = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq50943 eq51160
    | exact resolve eq51160 eq50943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51160
  have eq51765 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op x (τ (k X0 X0)))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq51098 eq666
    | exact resolve eq666 eq51098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666 eq51098
  have eq51777 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq583 eq51765
    | exact resolve eq51765 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583 eq51765
  have eq51872 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq51777
  have eq52521 : x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ x) ∨ x = y := by
    first
    | exact superpose eq51126 eq12789
    | exact resolve eq12789 eq51126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12789 eq51126
  have eq52594 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ x) := by grind
  clear eq52521
  have eq52639 : x = y ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq50943 eq52594
    | exact resolve eq52594 eq50943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50943 eq52594
  have eq52640 : (M.op x y) = (σ x) ∨ x = y := by grind
  clear eq52639
  have eq52787 : x = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq52640 eq29
    | exact resolve eq29 eq52640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq52640
  have eq52907 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq51185 eq52787
    | exact resolve eq52787 eq51185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51185 eq52787
  have eq52928 : x = y := by
    first
    | (have r₁ := eq52907
       have r₂ := eq51872
       grind)
    | exact resolve eq52907 eq51872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51872 eq52907
  have eq52947 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq52928
       grind)
    | exact superpose eq52928 eq18
    | exact resolve eq18 eq52928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq52948 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq52928
       grind)
    | exact superpose eq52928 eq24
    | exact resolve eq24 eq52928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq52928
  have eq52959 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq52948
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq52948
    | exact resolve eq52948 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52948
  have eq52960 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq52947
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq52947
    | exact resolve eq52947 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52947
  have eq52964 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq52959 eq26
    | exact resolve eq26 eq52959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq52959
  have eq53025 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq52964
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq52964
    | exact resolve eq52964 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq52964
  have eq53043 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq52960
       grind)
    | exact superpose eq52960 eq39
    | exact resolve eq39 eq52960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq52960
  have eq53314 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq53043
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq53043
    | exact resolve eq53043 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq53043
  have eq53373 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53025 eq53314
    | exact resolve eq53314 eq53025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53025 eq53314
  have eq53413 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq53373
    | exact resolve eq53373 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq53373
  have eq53443 : False := by grind
  exact eq53443

/-- `Equation1663`: `x = (x ◇ y) ◇ ((y ◇ z) ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(X,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_x_pyy_pyx_Equation1663 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1663 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1663.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq48 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
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
  clear eq36
  have eq53 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
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
  have eq58 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq69 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
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
  have eq84 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
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
  have eq105 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
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
  have eq113 : (k x y) = (τ (k (σ x) (σ y))) := by
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
  clear eq48
  have eq122 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq53 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq147 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | (have i₁ := eq58 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq58
    | (have j0 := eq58 y
       grind)
    | exact resolve eq58 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq156 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq69 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq69
    | exact resolve eq69 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq168 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq84 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq84
    | exact resolve eq84 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq202 : ∀ X0 X1 : G, x = (M.op (M.op x y) (M.op (M.op y X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0 X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : ∀ X0 X1 X2 X5 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X5)) = X1 := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq16 X1 (M.op X0 X2) (M.op (M.op X2 x) x) X5
       have i₂ := eq16 X0 X2 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 x (M.op (M.op x x) x)
       have i₂ := eq16 X0 x x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 X1 X2 X3 : G, (M.op (k X0 X1) (M.op (M.op X0 X2) X3)) = X1 ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X1 X0 X2 X3
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ x = y := by
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
  have eq217 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
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
  have eq219 : ∀ X0 X1 : G, (M.op (k X0 X1) X0) = X1 ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq208 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq208
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq208 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq208 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq208
    | (have j0 := eq208 y x
       grind)
    | exact resolve eq208 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq26 eq208
    | (have j0 := eq208 (σ y) (σ x)
       grind)
    | exact resolve eq208 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 X1)) ∨ (k X1 (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X0 X1)
       have i₂ := eq208 X1 X0
       grind)
    | exact superpose eq208 eq11
    | (have j0 := eq11 X1 (M.op X0 X1)
       grind)
    | exact resolve eq11 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 X1) X1 X2 X3
       have i₂ := eq208 X1 X0
       grind)
    | exact superpose eq208 eq16
    | exact resolve eq16 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op x X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq221 eq16
    | exact resolve eq16 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq222 eq16
    | exact resolve eq16 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ y) X0) X1) (M.op (σ x) (σ y))) ∨ (σ x) = (k (M.op (M.op (σ y) X0) X1) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq203 eq11
    | (have j0 := eq11 (M.op (M.op (σ y) X0) X1) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq426 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | exact superpose eq231 eq208
    | exact resolve eq208 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq442 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq237 eq208
    | exact resolve eq208 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1065 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq216
       grind)
    | exact superpose eq216 eq40
    | exact resolve eq40 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1066 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq1065
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1065
    | exact resolve eq1065 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065
  have eq1068 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq20 eq1066
    | exact resolve eq1066 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066
  have eq1075 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ X0 = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq11 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq11 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1090 : y ≠ (M.op x y) ∨ x = y ∨ (k x y) = (M.op y y) := by
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
  have eq1093 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1096 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ X0 = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1075 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075
  have eq1110 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1068 eq217
    | exact resolve eq217 eq1068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1117 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq1110
       have r₂ := eq27
       grind)
    | exact resolve eq1110 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110
  have eq1124 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1117 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1125 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1117 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1117
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1117
       grind)
    | exact resolve eq12 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1130 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1117 eq208
    | exact resolve eq208 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117
  have eq1134 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq1125
  have eq1135 : (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq1134
  have eq1136 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq1124
  have eq1142 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1130 eq1135
    | exact resolve eq1135 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130 eq1135
  have eq1143 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have j1 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq1136
       have r₂ := eq13 (σ x) (k (σ x) (σ y))
       grind)
    | (have r₁ := eq1136
       have r₂ := eq13 (k (σ x) (σ y)) (σ x)
       grind)
    | (have r₁ := eq1136
       have r₂ := eq13 (σ y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1136 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136
  have eq1147 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have j1 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq1142
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq1142
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq1142
       have r₂ := eq13 (σ y) (k (σ y) (σ x))
       grind)
    | exact resolve eq1142 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142
  have eq1148 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq26 eq1143
    | exact resolve eq1143 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143
  have eq1152 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1147 eq1068
    | exact resolve eq1068 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068
  have eq1156 : (τ (σ y)) = (k (τ (σ y)) x) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1147 eq156
    | exact resolve eq156 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147
  have eq1157 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq1152
  have eq1159 : y = (k y x) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq31 eq1156
    | exact resolve eq1156 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1156
  have eq1162 : y = (k y x) ∨ x = (M.op y x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq1159
       have r₂ := eq13 y (k y x)
       grind)
    | (have r₁ := eq1159
       have r₂ := eq13 (k y x) y
       grind)
    | (have r₁ := eq1159
       have r₂ := eq13 x (M.op y x)
       grind)
    | exact resolve eq1159 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1159
  have eq1167 : y = (M.op x y) ∨ x = (M.op y x) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq216
       have i₂ := eq1162
       grind)
    | exact superpose eq1162 eq216
    | exact resolve eq216 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq1169 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq1162
       grind)
    | exact superpose eq1162 eq40
    | exact resolve eq40 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162
  have eq1170 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq1167
  have eq1172 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1169
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1169
    | exact resolve eq1169 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169
  have eq1189 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x X0)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq202 x X0
       have i₂ := eq1157
       grind)
    | exact superpose eq1157 eq202
    | exact resolve eq202 eq1157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1192 : x ≠ x ∨ x = y ∨ (k y x) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq1157
       grind)
    | exact superpose eq1157 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1157
       grind)
    | exact resolve eq12 eq1157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1197 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq208 x y
       have i₂ := eq1157
       grind)
    | exact superpose eq1157 eq208
    | exact resolve eq208 eq1157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157
  have eq1201 : x ≠ x ∨ x = y ∨ (k y x) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1192
  have eq1202 : x = y ∨ (k y x) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1201
  have eq1209 : x = y ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1197 eq1202
    | exact resolve eq1202 eq1197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197 eq1202
  have eq1212 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1189 y
       have i₂ := eq426 sF0 x
       grind)
    | (have i₁ := eq1189 x
       have i₂ := eq426 sF0 x
       grind)
    | exact superpose eq426 eq1189
    | (have j0 := eq1189 y
       grind)
    | exact resolve eq1189 eq426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1189
  have eq1215 : y = (k y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq1209
       have r₂ := eq13 x y
       grind)
    | (have r₁ := eq1209
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq1209
       have r₂ := eq13 y (k y x)
       grind)
    | exact resolve eq1209 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209
  have eq1221 : (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq1215
       grind)
    | exact superpose eq1215 eq40
    | exact resolve eq40 eq1215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215
  have eq1222 : (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1221
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1221
    | exact resolve eq1221 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221
  have eq1228 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1222 eq217
    | exact resolve eq217 eq1222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1222
  have eq1239 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x X0)) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq202 x X0
       have i₂ := eq1170
       grind)
    | exact superpose eq1170 eq202
    | exact resolve eq202 eq1170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq1241 : x = (k x y) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq1170
       grind)
    | exact superpose eq1170 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq1170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1247 : y = (M.op x x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq208 x y
       have i₂ := eq1170
       grind)
    | exact superpose eq1170 eq208
    | exact resolve eq208 eq1170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170
  have eq1253 : x = (k x y) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq1241
  have eq1260 : x = (k x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq1253
       have r₂ := eq13 x (k x y)
       grind)
    | (have r₁ := eq1253
       have r₂ := eq13 (k x y) x
       grind)
    | (have r₁ := eq1253
       have r₂ := eq13 y (M.op x y)
       grind)
    | exact resolve eq1253 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253
  have eq1262 : x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1239 y
       have i₂ := eq426 sF0 x
       grind)
    | (have i₁ := eq1239 x
       have i₂ := eq426 sF0 x
       grind)
    | exact superpose eq426 eq1239
    | (have j0 := eq1239 y
       grind)
    | exact resolve eq1239 eq426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239
  have eq1266 : y = (M.op x y) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1260
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1260
    | exact resolve eq1260 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1260
  have eq1267 : x = (k x y) ∨ y = (M.op x y) := by grind
  clear eq1266
  have eq1280 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1267
       grind)
    | exact superpose eq1267 eq41
    | exact resolve eq41 eq1267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1281 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1280
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1280
    | exact resolve eq1280 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1280
  have eq1326 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1212 eq208
    | exact resolve eq208 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1339 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) y) = X0 ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq231 X0 x
       have i₂ := eq1247
       grind)
    | exact superpose eq1247 eq231
    | exact resolve eq231 eq1247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231 eq1247
  have eq1362 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1262 eq208
    | exact resolve eq208 eq1262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262
  have eq1373 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (k x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1326 eq12
    | (have j0 := eq12 x (M.op x y)
       grind)
    | (have r₁ := eq12 x (M.op x y)
       have r₂ := eq1326
       grind)
    | exact resolve eq12 eq1326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326
  have eq1382 : x = (M.op x y) ∨ (k x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq1373
  have eq1385 : x = (M.op x y) ∨ x = (k x (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1212 eq1382
    | exact resolve eq1382 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212 eq1382
  have eq1389 : x = (k x (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x (M.op x y)
       grind)
    | (have r₁ := eq1385
       have r₂ := eq13 x (M.op x y)
       grind)
    | (have r₁ := eq1385
       have r₂ := eq13 (M.op x y) x
       grind)
    | (have r₁ := eq1385
       have r₂ := eq13 x (k x (M.op x y))
       grind)
    | exact resolve eq1385 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1385
  have eq1412 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1389 eq42
    | exact resolve eq42 eq1389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1389
  have eq1413 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1412
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1412
    | exact resolve eq1412 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412
  have eq1538 : ∀ X0 : G, (M.op (k (M.op x y) X0) y) = X0 ∨ y = (M.op x y) ∨ x = y ∨ (M.op (M.op x y) X0) = X0 ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have i₁ := eq1339 x
       have i₂ := eq11 sF0 x
       grind)
    | exact superpose eq11 eq1339
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq1339 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339
  have eq1875 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq1228 eq203
    | exact resolve eq203 eq1228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1884 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1228 eq208
    | exact resolve eq208 eq1228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228
  have eq1901 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq442 eq1875
    | (have j0 := eq1875 (σ y)
       grind)
    | exact resolve eq1875 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1875
  have eq1983 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1901 eq208
    | exact resolve eq208 eq1901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1901
  have eq2665 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1148 eq168
    | exact resolve eq168 eq1148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168 eq1148
  have eq2668 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq29 eq2665
    | exact resolve eq2665 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2665
  have eq2671 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq2668
       have r₂ := eq13 x (k x y)
       grind)
    | (have r₁ := eq2668
       have r₂ := eq13 (k x y) x
       grind)
    | (have r₁ := eq2668
       have r₂ := eq13 (σ y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq2668 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2668
  have eq2674 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1267 eq2671
    | exact resolve eq2671 eq1267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2671
  have eq2679 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq2674
       grind)
    | exact superpose eq2674 eq41
    | exact resolve eq41 eq2674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq2674
  have eq2682 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq2679
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2679
    | exact resolve eq2679 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2679
  have eq2723 : ∀ X0 X1 X2 X3 : G, (σ X1) = (M.op (σ (k X0 X1)) (M.op (M.op (σ X0) X2) X3)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq213 (σ X0) (σ X1) X2 X3
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq213
    | (have j0 := eq213 (σ X0) (σ X1) X2 X3
       grind)
    | exact resolve eq213 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2737 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (M.op (M.op (σ x) X0) X1)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) := by
    intro X0 X1
    first
    | exact superpose eq2682 eq213
    | (have j0 := eq213 (σ x) (σ y) x x
       grind)
    | exact resolve eq213 eq2682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2742 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (M.op (σ x) X0) X1)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq1413 eq213
    | (have j0 := eq213 (σ x) (σ (M.op x y)) x x
       grind)
    | exact resolve eq213 eq1413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2747 : ∀ X0 X1 : G, (σ x) = (M.op (σ y) (M.op (M.op (σ y) X0) X1)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq1172 eq213
    | (have j0 := eq213 (σ y) (σ x) x x
       grind)
    | exact resolve eq213 eq1172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq2891 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2747 x x
       have i₂ := eq227 sF3 sF3 x x
       grind)
    | exact superpose eq227 eq2747
    | exact resolve eq2747 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2747
  have eq2894 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2742 x x
       have i₂ := eq227 sF2 sF2 x x
       grind)
    | exact superpose eq227 eq2742
    | exact resolve eq2742 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2742
  have eq2899 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq2737 x x
       have i₂ := eq227 sF2 sF2 x x
       grind)
    | exact superpose eq227 eq2737
    | exact resolve eq2737 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2737
  have eq2908 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2723 X0 X1 x x
       have i₂ := eq227 (σ (k X0 X1)) (σ X0) x x
       grind)
    | exact superpose eq227 eq2723
    | (have j0 := eq2723 X0 X1 x x
       grind)
    | exact resolve eq2723 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2723
  have eq2910 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq26 eq2899
    | exact resolve eq2899 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2899
  have eq2911 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) x) := by grind
  clear eq2910
  have eq2929 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq2682 eq1096
    | (have j0 := eq1096 (σ x) (σ y)
       grind)
    | (have r₁ := eq1096 (σ x) (σ y)
       have r₂ := eq2682
       grind)
    | exact resolve eq1096 eq2682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2682
  have eq2934 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (k (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1413 eq1096
    | (have j0 := eq1096 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq1096 (σ x) (σ (M.op x y))
       have r₂ := eq1413
       grind)
    | exact resolve eq1096 eq1413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2939 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1172 eq1096
    | (have j0 := eq1096 (σ y) (σ x)
       grind)
    | (have r₁ := eq1096 (σ y) (σ x)
       have r₂ := eq1172
       grind)
    | exact resolve eq1096 eq1172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172
  have eq2945 : (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq2939
  have eq2950 : (σ (M.op x y)) = (σ x) ∨ (k (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq2934
  have eq2955 : (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) := by grind
  clear eq2929
  have eq2969 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2891 eq2945
    | exact resolve eq2945 eq2891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2891 eq2945
  have eq2972 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2894 eq2950
    | exact resolve eq2950 eq2894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2950
  have eq2979 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq26 eq2955
    | exact resolve eq2955 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2955
  have eq2980 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op (M.op x y) x) := by grind
  clear eq2979
  have eq2993 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have j1 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq2969
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq2969
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq2969
       have r₂ := eq13 (σ x) (k (σ x) (σ y))
       grind)
    | exact resolve eq2969 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2969
  have eq2995 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq2972
       have r₂ := eq13 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq2972
       have r₂ := eq13 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq2972
       have r₂ := eq13 (σ (M.op x y)) (k (σ (M.op x y)) (σ x))
       grind)
    | exact resolve eq2972 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2972
  have eq3000 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq2911 eq2980
    | exact resolve eq2980 eq2911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2911 eq2980
  have eq3008 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1281 eq2993
    | exact resolve eq2993 eq1281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2993
  have eq3010 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have j1 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq3000
       have r₂ := eq13 (σ y) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq3000
       have r₂ := eq13 (M.op (σ x) (σ y)) (σ y)
       grind)
    | (have r₁ := eq3000
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq3000 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3000
  have eq3040 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq3010 eq1096
    | (have j0 := eq1096 (σ x) (σ y)
       grind)
    | (have r₁ := eq1096 (σ y) (σ x)
       have r₂ := eq3010
       grind)
    | exact resolve eq1096 eq3010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3010
  have eq3043 : (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) := by grind
  clear eq3040
  have eq3047 : (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have r₁ := eq3043
       have r₂ := eq1093
       grind)
    | exact resolve eq3043 eq1093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3043
  have eq3051 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq3008 eq3047
    | exact resolve eq3047 eq3008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3008 eq3047
  have eq4668 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2995 eq1096
    | (have j0 := eq1096 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq1096 (σ (M.op x y)) (σ x)
       have r₂ := eq2995
       grind)
    | exact resolve eq1096 eq2995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2995
  have eq4671 : (σ (M.op x y)) = (σ x) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq4668
  have eq4674 : (σ (M.op x y)) = (σ x) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq12 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq4671
       have r₂ := eq12 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq4671
       have r₂ := eq12 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq4671 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4671
  have eq4679 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1413 eq4674
    | exact resolve eq4674 eq1413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1413 eq4674
  have eq9088 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2894 eq1884
    | exact resolve eq1884 eq2894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2894
  have eq9122 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq9088
  have eq9848 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq4679 eq208
    | exact resolve eq208 eq4679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4679
  have eq10748 : ∀ X0 X1 : G, (M.op (M.op X0 (σ (M.op x y))) (M.op (σ x) X1)) = X0 ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq9848 eq16
    | exact resolve eq16 eq9848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10759 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X1)) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq9848 eq227
    | exact resolve eq227 eq9848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10769 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq442 eq10759
    | (have j0 := eq10759 X0 (σ y)
       grind)
    | exact resolve eq10759 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10759
  have eq10774 : ∀ X0 : G, (M.op (M.op X0 (σ (M.op x y))) (M.op (σ x) (σ y))) = X0 ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq442 eq10748
    | (have j0 := eq10748 X0 (σ y)
       grind)
    | exact resolve eq10748 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10748
  have eq21202 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq10769 eq1983
    | exact resolve eq1983 eq10769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1983 eq10769
  have eq21266 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq21202
  have eq21338 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq1884 eq21266
    | exact resolve eq21266 eq1884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1884 eq21266
  have eq21339 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq21338
  have eq21365 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq9122 eq21339
    | exact resolve eq21339 eq9122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9122 eq21339
  have eq21371 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq21365
       have r₂ := eq27
       grind)
    | exact resolve eq21365 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21365
  have eq21383 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq21371 eq222
    | exact resolve eq222 eq21371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq21603 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq9848 eq10774
    | exact resolve eq10774 eq9848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9848 eq10774
  have eq21709 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq21603
  have eq21725 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq21371 eq21709
    | exact resolve eq21709 eq21371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21709
  have eq21816 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq21725
  have eq21829 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq21816
    | exact resolve eq21816 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21816
  have eq21831 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq21829
       have r₂ := eq27
       grind)
    | exact resolve eq21829 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21829
  have eq21845 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ (M.op x y))) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq21831 eq237
    | exact resolve eq237 eq21831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21831
  have eq21910 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ (M.op x y))) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq21371 eq21845
    | exact resolve eq21845 eq21371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21845
  have eq22113 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq21910
    | (have j0 := eq21910 (σ x)
       grind)
    | exact resolve eq21910 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21910
  have eq22187 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21371 eq22113
    | exact resolve eq22113 eq21371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21371 eq22113
  have eq22311 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq22187 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq11 eq22187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22187
  have eq22330 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq22311
  have eq29616 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq22330 eq208
    | exact resolve eq208 eq22330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22330
  have eq29663 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21383 eq29616
    | exact resolve eq29616 eq21383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21383 eq29616
  have eq29664 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq29663
  have eq29687 : (τ (σ x)) = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29664 eq147
    | exact resolve eq147 eq29664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29664
  have eq29702 : x = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29 eq29687
    | exact resolve eq29687 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29687
  have eq29720 : y = (M.op x (M.op x y)) ∨ y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29702 eq219
    | (have j0 := eq219 (M.op x y) y
       grind)
    | exact resolve eq219 eq29702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29702
  have eq29740 : x = y ∨ y = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq221 eq29720
    | exact resolve eq29720 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29720
  have eq29741 : x = y ∨ y = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq29740
  have eq29753 : x = y ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1362 eq29741
    | exact resolve eq29741 eq1362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1362 eq29741
  have eq29754 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq29753
  have eq29765 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq29754 eq31
    | exact resolve eq31 eq29754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29754
  have eq29846 : x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq29 eq29765
    | exact resolve eq29765 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29765
  have eq29847 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq29846
  have eq29854 : (M.op x y) = (τ (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq29847 eq28
    | exact resolve eq28 eq29847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29847
  have eq29964 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq31 eq29854
    | exact resolve eq29854 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29854
  have eq29965 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq29964
  have eq29980 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29965 eq28
    | exact resolve eq28 eq29965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29992 : (k (M.op x y) y) = (τ (k (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29965 eq147
    | exact resolve eq147 eq29965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq29965
  have eq30090 : (k x y) = (k (M.op x y) y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq113 eq29992
    | exact resolve eq29992 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq29992
  have eq30102 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq29980
    | exact resolve eq29980 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29980
  have eq30105 : x = (k (M.op x y) y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1267 eq30090
    | exact resolve eq30090 eq1267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1267 eq30090
  have eq30111 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30102 eq30105
    | exact resolve eq30105 eq30102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30102 eq30105
  have eq30113 : (M.op x y) = (k (M.op x y) y) ∨ x = y := by
    first
    | (have j1 := eq13 (M.op x y) y
       grind)
    | (have r₁ := eq30111
       have r₂ := eq13 (M.op x y) (k (M.op x y) y)
       grind)
    | (have r₁ := eq30111
       have r₂ := eq13 (k (M.op x y) y) (M.op x y)
       grind)
    | (have r₁ := eq30111
       have r₂ := eq13 y (M.op x y)
       grind)
    | exact resolve eq30111 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30111
  have eq30142 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30113 eq1538
    | (have j0 := eq1538 y
       grind)
    | exact resolve eq1538 eq30113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538 eq30113
  have eq30160 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq30142
  have eq30189 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq221 eq30160
    | exact resolve eq30160 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30160
  have eq30190 : y = (M.op x y) ∨ x = y := by grind
  clear eq30189
  have eq30215 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq30190
       grind)
    | exact superpose eq30190 eq18
    | exact resolve eq18 eq30190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30216 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq30190
       grind)
    | exact superpose eq30190 eq24
    | exact resolve eq24 eq30190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30221 : x = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq221
       have i₂ := eq30190
       grind)
    | exact superpose eq30190 eq221
    | exact resolve eq221 eq30190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30222 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (k x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq1090
       have i₂ := eq30190
       grind)
    | exact superpose eq30190 eq1090
    | (have r₁ := eq1090
       have r₂ := eq30190
       grind)
    | exact resolve eq1090 eq30190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090
  have eq30245 : x ≠ (M.op x y) ∨ x = y := by grind
  have eq30246 : x = (M.op x y) ∨ (k x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by grind
  clear eq30222
  have eq30260 : (k x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have r₁ := eq30246
       have r₂ := eq30245
       grind)
    | exact resolve eq30246 eq30245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30246
  have eq30265 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq30216
    | exact resolve eq30216 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30216
  have eq30268 : x = (k x (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq30221 eq30260
    | exact resolve eq30260 eq30221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30260
  have eq30531 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq30268 eq42
    | exact resolve eq42 eq30268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq30268
  have eq30545 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq30531
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30531
    | exact resolve eq30531 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30531
  have eq30549 : (σ x) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq30265 eq30545
    | exact resolve eq30545 eq30265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30545
  have eq30551 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1281 eq30549
    | exact resolve eq30549 eq1281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281 eq30549
  have eq30559 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30551 eq219
    | (have j0 := eq219 (σ x) (σ y)
       grind)
    | exact resolve eq219 eq30551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30560 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30551 eq1096
    | (have j0 := eq1096 (σ x) (σ y)
       grind)
    | (have r₁ := eq1096 (σ x) (σ y)
       have r₂ := eq30551
       grind)
    | exact resolve eq1096 eq30551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30563 : (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq30560
  have eq30566 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq30563
    | exact resolve eq30563 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30563
  have eq30567 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq30559
    | exact resolve eq30559 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30559
  have eq32548 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30566 eq30567
    | exact resolve eq30567 eq30566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30566 eq30567
  have eq32595 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq32548
  have eq32623 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq32595
       have r₂ := eq13 (σ y) (k (σ y) (σ x))
       grind)
    | (have r₁ := eq32595
       have r₂ := eq13 (k (σ y) (σ x)) (σ y)
       grind)
    | (have r₁ := eq32595
       have r₂ := eq13 (σ y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq32595 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32595
  have eq32651 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32623 eq1096
    | (have j0 := eq1096 (σ x) (σ y)
       grind)
    | (have r₁ := eq1096 (σ y) (σ x)
       have r₂ := eq32623
       grind)
    | exact resolve eq1096 eq32623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1096 eq32623
  have eq32654 : (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq32651
  have eq32659 : (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq32654
       have r₂ := eq1093
       grind)
    | exact resolve eq32654 eq1093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093 eq32654
  have eq32663 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30551 eq32659
    | exact resolve eq32659 eq30551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30551 eq32659
  have eq44487 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq3051 eq225
    | (have j0 := eq225 (σ y) (σ x)
       grind)
    | exact resolve eq225 eq3051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3051
  have eq44492 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32663 eq225
    | (have j0 := eq225 (σ y) (σ x)
       grind)
    | exact resolve eq225 eq32663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32663
  have eq44887 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq44492
  have eq44890 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) x) := by grind
  clear eq44487
  have eq45027 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq44887
       have r₂ := eq13 (σ x) (M.op (σ y) (σ x))
       grind)
    | (have r₁ := eq44887
       have r₂ := eq13 (M.op (σ y) (σ x)) (σ x)
       grind)
    | (have r₁ := eq44887
       have r₂ := eq13 (σ y) (k (σ y) (σ x))
       grind)
    | exact resolve eq44887 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44887
  have eq45028 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have j1 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq44890
       have r₂ := eq13 (σ x) (M.op (σ y) (σ x))
       grind)
    | (have r₁ := eq44890
       have r₂ := eq13 (M.op (σ y) (σ x)) (σ x)
       grind)
    | (have r₁ := eq44890
       have r₂ := eq13 (σ y) (k (σ y) (σ x))
       grind)
    | exact resolve eq44890 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44890
  have eq45100 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq45027 eq45028
    | exact resolve eq45028 eq45027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45027 eq45028
  have eq45611 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq45100 eq217
    | exact resolve eq217 eq45100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45100
  have eq45635 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq45611
  have eq46070 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq45635 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq45635
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq45635
       grind)
    | (have r₁ := eq12 (M.op x y) (M.op x y)
       have r₂ := eq45635
       grind)
    | exact resolve eq12 eq45635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46076 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq45635 eq208
    | exact resolve eq208 eq45635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45635
  have eq46089 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq46070
  have eq46090 : (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq46089
  have eq46132 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq46076 eq46090
    | exact resolve eq46090 eq46076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46076 eq46090
  have eq46140 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq46132
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq46132
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq46132
       have r₂ := eq13 (σ y) (k (σ y) (σ x))
       grind)
    | exact resolve eq46132 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46132
  have eq46159 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq46140 eq156
    | exact resolve eq156 eq46140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156 eq46140
  have eq46174 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    first
    | exact superpose eq31 eq46159
    | exact resolve eq46159 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46159
  have eq46212 : x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    first
    | exact superpose eq46174 eq30221
    | exact resolve eq30221 eq46174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30221 eq46174
  have eq46266 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    first
    | (have r₁ := eq46212
       have r₂ := eq30245
       grind)
    | exact resolve eq46212 eq30245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46212
  have eq46275 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq46266
       have r₂ := eq13 x y
       grind)
    | (have r₁ := eq46266
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq46266
       have r₂ := eq13 (σ y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq46266 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46266
  have eq46294 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq46275
       grind)
    | exact superpose eq46275 eq40
    | exact resolve eq40 eq46275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq46275
  have eq46314 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq46294
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq46294
    | exact resolve eq46294 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46294
  have eq46329 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq46314 eq217
    | exact resolve eq217 eq46314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq46314
  have eq46351 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq46329
  have eq46362 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq46351 eq203
    | exact resolve eq203 eq46351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq46426 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq46351 eq227
    | exact resolve eq227 eq46351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227 eq46351
  have eq46468 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq442 eq46426
    | (have j0 := eq46426 X0 (σ y)
       grind)
    | exact resolve eq46426 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46426
  have eq46479 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq442 eq46362
    | (have j0 := eq46362 (σ y)
       grind)
    | exact resolve eq46362 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46362
  have eq46994 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = X0 ∨ (k X0 (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq46468 eq12
    | (have j0 := eq12 (M.op (σ x) (σ y)) X0
       grind)
    | (have r₁ := eq12 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq46468 (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq46468 X0
       grind)
    | exact resolve eq12 eq46468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47271 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = X0 ∨ (σ x) = (k X0 (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq46479 eq46994
    | (have j0 := eq46994 X0
       grind)
    | exact resolve eq46994 eq46479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46479 eq46994
  have eq67078 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ y) X0) X1) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (M.op (M.op (σ y) X0) X1) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq257 eq46468
    | (have j1 := eq257 X0 X1
       grind)
    | exact resolve eq46468 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257 eq46468
  have eq67149 : ∀ X0 X1 : G, (σ x) = (k (M.op (M.op (σ y) X0) X1) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq67078 X0 X1
       have j1 := eq47271 (M.op (M.op (σ y) X0) X1)
       grind)
    | (have r₁ := eq67078 X0 X1
       have r₂ := eq47271 (M.op (M.op (σ y) X0) X1)
       grind)
    | (have r₁ := eq67078 X0 (σ y)
       have r₂ := eq47271 (M.op (σ y) X0)
       grind)
    | exact resolve eq67078 eq47271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47271 eq67078
  have eq77367 : (σ x) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq237 eq67149
    | exact resolve eq67149 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237 eq67149
  have eq77522 : (σ x) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq77367
  have eq77702 : (τ (σ x)) = (k y (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq77522 eq122
    | exact resolve eq122 eq77522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq77522
  have eq77729 : x = (k y (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq77702
    | exact resolve eq77702 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77702
  have eq77731 : x = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq77729
       have i₂ := eq30190
       grind)
    | exact superpose eq30190 eq77729
    | exact resolve eq77729 eq30190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30190 eq77729
  have eq77814 : (M.op x (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq77731 eq219
    | (have j0 := eq219 (M.op x y) (τ (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq219 eq77731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77825 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq30215 eq77814
    | exact resolve eq77814 eq30215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30215 eq77814
  have eq77826 : (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq77825
  have eq78121 : (τ (M.op (σ x) (σ y))) ≠ (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq77826 eq12
    | (have j0 := eq12 (M.op x y) (τ (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq12 (M.op x y) (τ (M.op (σ x) (σ y)))
       have r₂ := eq77826
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq77826
       grind)
    | exact resolve eq12 eq77826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78127 : (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq77826 eq208
    | exact resolve eq208 eq77826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77826
  have eq78143 : (τ (M.op (σ x) (σ y))) ≠ (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq78121
  have eq78144 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq78143
  have eq78157 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq78127 eq78144
    | exact resolve eq78144 eq78127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78127 eq78144
  have eq78161 : (M.op x y) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have j1 := eq13 (M.op x y) (τ (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq78157
       have r₂ := eq13 (M.op x y) (τ (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq78157
       have r₂ := eq13 (τ (M.op (σ x) (σ y))) (M.op x y)
       grind)
    | (have r₁ := eq78157
       have r₂ := eq13 (M.op x y) (k (M.op x y) (τ (M.op (σ x) (σ y))))
       grind)
    | exact resolve eq78157 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78157
  have eq78163 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq78161 eq77731
    | exact resolve eq77731 eq78161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77731 eq78161
  have eq78181 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq78163
  have eq78189 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq78181
       have r₂ := eq30245
       grind)
    | exact resolve eq78181 eq30245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30245 eq78181
  have eq78199 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq78189 eq27
    | exact resolve eq27 eq78189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78189
  have eq78339 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq78199
       have r₂ := eq30265
       grind)
    | exact resolve eq78199 eq30265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30265 eq78199
  have eq78356 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq78339 eq31
    | exact resolve eq31 eq78339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq78339
  have eq78575 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq78356
    | exact resolve eq78356 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78356
  have eq78576 : x = y := by grind
  clear eq78575
  have eq78649 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq78576
       grind)
    | exact superpose eq78576 eq18
    | exact resolve eq18 eq78576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq78650 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq78576
       grind)
    | exact superpose eq78576 eq24
    | exact resolve eq24 eq78576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq78654 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq221
       have i₂ := eq78576
       grind)
    | exact superpose eq78576 eq221
    | exact resolve eq221 eq78576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221 eq78576
  have eq78685 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq78650
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq78650
    | exact resolve eq78650 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78650
  have eq78686 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq78685 eq26
    | exact resolve eq26 eq78685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq78685
  have eq78907 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq225 x x
       have i₂ := eq78649
       grind)
    | exact superpose eq78649 eq225
    | (have j0 := eq225 x (M.op x y)
       grind)
    | exact resolve eq225 eq78649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78922 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (k x (M.op x y)) := by
    first
    | (have j1 := eq13 x (M.op x y)
       grind)
    | (have r₁ := eq78907
       have r₂ := eq13 (M.op x y) (M.op x (M.op x y))
       grind)
    | (have r₁ := eq78907
       have r₂ := eq13 (M.op x (M.op x y)) (M.op x y)
       grind)
    | (have r₁ := eq78907
       have r₂ := eq13 x (k x (M.op x y))
       grind)
    | exact resolve eq78907 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78907
  have eq80108 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq78686 eq225
    | (have j0 := eq225 (σ x) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq225 eq78686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80134 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have j1 := eq13 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq80108
       have r₂ := eq13 (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq80108
       have r₂ := eq13 (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq80108
       have r₂ := eq13 (σ x) (k (σ x) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq80108 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80108
  have eq81352 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (k x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq78922 eq12
    | (have j0 := eq12 x (M.op x y)
       grind)
    | (have r₁ := eq12 x (M.op x y)
       have r₂ := eq78922
       grind)
    | exact resolve eq12 eq78922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81358 : x = (k x (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq78922 eq208
    | exact resolve eq208 eq78922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78922
  have eq81374 : x = (M.op x y) ∨ (k x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) := by grind
  clear eq81352
  have eq81389 : (k x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) := by
    first
    | (have j1 := eq13 x (M.op x y)
       grind)
    | (have r₁ := eq81374
       have r₂ := eq13 x (M.op x y)
       grind)
    | (have r₁ := eq81374
       have r₂ := eq13 (M.op x y) x
       grind)
    | (have r₁ := eq81374
       have r₂ := eq13 (k x (M.op x y)) (M.op (M.op x y) (M.op x y))
       grind)
    | exact resolve eq81374 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81374
  have eq81391 : x = (k x (M.op x y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq81358 eq81389
    | exact resolve eq81389 eq81358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81358 eq81389
  have eq81392 : x = (k x (M.op x y)) := by grind
  clear eq81391
  have eq81423 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq81392 eq2908
    | (have j0 := eq2908 x (M.op x y)
       grind)
    | exact resolve eq2908 eq81392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81392
  have eq81426 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq81423
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq81423
    | exact resolve eq81423 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81423
  have eq81433 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq78686 eq81426
    | exact resolve eq81426 eq78686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81426
  have eq81437 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq81433
    | exact resolve eq81433 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81433
  have eq81439 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ (M.op x y)) := by
    first
    | (have r₁ := eq81437
       have r₂ := eq27
       grind)
    | exact resolve eq81437 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81437
  have eq81441 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq81439
    | exact resolve eq81439 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81439
  have eq81443 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq81441
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq81441
    | exact resolve eq81441 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81441
  have eq81445 : (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq81443
    | exact resolve eq81443 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81443
  have eq81447 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq81445
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq81445
    | exact resolve eq81445 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81445
  have eq81503 : ∀ X0 X1 : G, (M.op (M.op X0 (σ (M.op x y))) (M.op (σ x) X1)) = X0 ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq81447 eq207
    | exact resolve eq207 eq81447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq81505 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq81447 eq208
    | exact resolve eq208 eq81447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81549 : ∀ X0 : G, (M.op (M.op X0 (σ (M.op x y))) (M.op (σ x) (σ y))) = X0 ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq442 eq81503
    | (have j0 := eq81503 X0 (σ y)
       grind)
    | exact resolve eq81503 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442 eq81503
  have eq81706 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq80134 eq12
    | (have j0 := eq12 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq80134
       grind)
    | exact resolve eq12 eq80134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81712 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq80134 eq208
    | exact resolve eq208 eq80134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80134
  have eq81728 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq81706
  have eq81739 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have j1 := eq13 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq81728
       have r₂ := eq13 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq81728
       have r₂ := eq13 (M.op (σ x) (σ y)) (σ x)
       grind)
    | (have r₁ := eq81728
       have r₂ := eq13 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (σ x) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq81728 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81728
  have eq81747 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq81712 eq81739
    | exact resolve eq81739 eq81712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81712 eq81739
  have eq81748 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq81747
  have eq81753 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq81748 eq105
    | exact resolve eq105 eq81748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq81748
  have eq81770 : x = (k x (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq29 eq81753
    | exact resolve eq81753 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81753
  have eq81786 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ (τ (M.op (σ x) (σ y))) = (M.op x (τ (M.op (σ x) (σ y)))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq81770 eq219
    | (have j0 := eq219 x (τ (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq219 eq81770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq81770
  have eq81797 : (τ (M.op (σ x) (σ y))) = (M.op x (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq81786
       have i₂ := eq78649
       grind)
    | exact superpose eq78649 eq81786
    | exact resolve eq81786 eq78649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78649 eq81786
  have eq82340 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq81505 eq81549
    | exact resolve eq81549 eq81505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81505
  have eq82348 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq81447 eq81549
    | exact resolve eq81549 eq81447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81549
  have eq82460 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq82348
  have eq82466 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq82340
  have eq89597 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq81797 eq426
    | exact resolve eq426 eq81797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq89606 : x = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq81797 eq208
    | exact resolve eq208 eq81797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq92025 : (M.op x (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq89597 eq81797
    | exact resolve eq81797 eq89597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81797 eq89597
  have eq92171 : (M.op x (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq92025
  have eq92223 : (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ x = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq92171 eq225
    | (have j0 := eq225 (M.op x y) (τ (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq225 eq92171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq92235 : (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ x = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq92223
  have eq119962 : (τ (M.op (σ x) (σ y))) ≠ (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ x = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq92235 eq12
    | (have j0 := eq12 (M.op x y) (τ (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq12 (M.op x y) (τ (M.op (σ x) (σ y)))
       have r₂ := eq92235
       grind)
    | exact resolve eq12 eq92235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92235
  have eq119991 : (τ (M.op (σ x) (σ y))) ≠ (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ x = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq119962
  have eq119992 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ x = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq119991
  have eq120023 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ x = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq89606 eq119992
    | exact resolve eq119992 eq89606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89606 eq119992
  have eq120024 : x = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq120023
  have eq120064 : (σ (τ (M.op (σ x) (σ y)))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (τ (M.op (σ x) (σ y)))) = (M.op (σ (M.op x y)) (σ (τ (M.op (σ x) (σ y))))) ∨ (σ (M.op x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq120024 eq2908
    | (have j0 := eq2908 (M.op x y) (τ (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq2908 eq120024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2908 eq120024
  have eq120080 : (σ (τ (M.op (σ x) (σ y)))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (τ (M.op (σ x) (σ y)))) = (M.op (σ (M.op x y)) (σ (τ (M.op (σ x) (σ y))))) ∨ (σ (M.op x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20 eq120064
    | exact resolve eq120064 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120064
  have eq120091 : (M.op (σ x) (σ (M.op x y))) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ (τ (M.op (σ x) (σ y)))) = (M.op (σ (M.op x y)) (σ (τ (M.op (σ x) (σ y))))) ∨ (σ (M.op x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq120080
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq120080
    | exact resolve eq120080 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120080
  have eq120099 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (τ (M.op (σ x) (σ y)))) = (M.op (σ (M.op x y)) (σ (τ (M.op (σ x) (σ y))))) ∨ (σ (M.op x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq120091
       have i₂ := eq14 sF4
       grind)
    | exact superpose eq14 eq120091
    | exact resolve eq120091 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120091
  have eq120101 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq120099
       have i₂ := eq14 sF4
       grind)
    | exact superpose eq14 eq120099
    | exact resolve eq120099 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120099
  have eq120102 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20 eq120101
    | exact resolve eq120101 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120101
  have eq120103 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq120102
       have i₂ := eq14 sF4
       grind)
    | exact superpose eq14 eq120102
    | exact resolve eq120102 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120102
  have eq120104 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20 eq120103
    | exact resolve eq120103 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120103
  have eq120105 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq120104
       have r₂ := eq27
       grind)
    | exact resolve eq120104 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120104
  have eq120178 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq120105 eq81447
    | exact resolve eq81447 eq120105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81447 eq120105
  have eq120261 : (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq120178
       have r₂ := eq27
       grind)
    | exact resolve eq120178 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120178
  have eq120270 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq82460 eq120261
    | exact resolve eq120261 eq82460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82460 eq120261
  have eq120322 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq120270 eq14
    | exact resolve eq14 eq120270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120270
  have eq120347 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20 eq120322
    | exact resolve eq120322 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120322
  have eq120358 : x = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq120347
       have r₂ := eq27
       grind)
    | exact resolve eq120347 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120347
  have eq120397 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq120358 eq14
    | exact resolve eq14 eq120358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120358
  have eq120422 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq120397
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq120397
    | exact resolve eq120397 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq120397
  have eq120423 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq120422
  have eq120631 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq120423 eq82466
    | exact resolve eq82466 eq120423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82466 eq120423
  have eq120685 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq120631
  have eq120821 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq78686 eq120685
    | exact resolve eq120685 eq78686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78686 eq120685
  have eq120849 : (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq120821
       have r₂ := eq27
       grind)
    | exact resolve eq120821 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120821
  have eq120864 : (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq120849 eq28
    | exact resolve eq28 eq120849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq120849
  have eq120959 : x = (M.op x y) := by
    first
    | exact superpose eq120864 eq29
    | exact resolve eq29 eq120864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq120864
  have eq121082 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq78654
       have i₂ := eq120959
       grind)
    | exact superpose eq120959 eq78654
    | exact resolve eq78654 eq120959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78654
  have eq121106 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq92171
       have i₂ := eq120959
       grind)
    | exact superpose eq120959 eq92171
    | exact resolve eq92171 eq120959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92171 eq120959
  have eq121125 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq121106
  have eq126533 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq121125 eq121082
    | exact resolve eq121082 eq121125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121082 eq121125
  have eq126595 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq126533
  have eq126676 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq126595 eq14
    | exact resolve eq14 eq126595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126595
  have eq126693 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq126676
    | exact resolve eq126676 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq126676
  have eq126699 : False := by grind
  exact eq126699

/-- `Equation168`: `x = (y ◇ x) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if X = Y then Y else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyx_y_x_Equation168 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) Law168 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law168.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq30 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X0) X1 (M.op X0 x)
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq15
    | (have j0 := eq15 X0 (M.op x y)
       grind)
    | exact resolve eq15 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15
    | (have j0 := eq15 y X0
       grind)
    | exact resolve eq15 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq9 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9
    | (have j0 := eq9 x X0 y
       grind)
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq9 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9
    | (have j0 := eq9 y x X0
       grind)
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) ≠ X0 ∨ (k (M.op X0 X2) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 X2) (M.op X1 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq59 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ X0 ∨ (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq9 X0 X0 X0
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq56 eq9
    | exact resolve eq9 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq60 (σ X0)
       grind)
    | exact superpose eq60 eq15
    | exact resolve eq15 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq74 X0
       have i₂ := eq60 X0
       grind)
    | exact superpose eq60 eq74
    | exact resolve eq74 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq100 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq33 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq33
    | (have j0 := eq33 y
       grind)
    | exact resolve eq33 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq108 : (k (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq34 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq34
    | (have j0 := eq34 y
       grind)
    | exact resolve eq34 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq126 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq134 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq108
    | (have j1 := eq14 (σ y) (σ (k y x))
       grind)
    | exact resolve eq108 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq137 : (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq134
    | exact resolve eq134 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq218 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq10
    | exact resolve eq10 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 : G, (σ (k y (M.op X0 X0))) = (k (σ y) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq36 (M.op X0 X0)
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq36
    | exact resolve eq36 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq264 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq218 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq218
    | exact resolve eq218 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq394 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X0 X1
       have i₂ := eq9 X0 X0 X0
       grind)
    | exact superpose eq9 eq57
    | (have j0 := eq57 X0 X0 X1
       grind)
    | (have r₁ := eq57 x x x
       have r₂ := eq9 x x x
       grind)
    | exact resolve eq57 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq395 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq394 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq399 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq71 eq59
    | (have r₁ := eq59 (M.op x y) y
       have r₂ := eq71 (M.op x y)
       grind)
    | exact resolve eq59 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq400 : x ≠ x ∨ x = (k (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq55 eq59
    | (have r₁ := eq59 x (M.op x y)
       have r₂ := eq55 x
       grind)
    | exact resolve eq59 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq406 : x = (k (M.op x y) (M.op x x)) := by grind
  clear eq400
  have eq407 : (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by grind
  clear eq399
  have eq591 : (σ y) = (σ (M.op x y)) ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq407 eq126
    | (have j0 := eq126 y (M.op (M.op x y) (M.op x y))
       grind)
    | exact resolve eq126 eq407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq593 : (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | exact superpose eq406 eq126
    | (have j0 := eq126 (M.op x y) (M.op x x)
       grind)
    | exact resolve eq126 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq614 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq126 X0 X1
       grind)
    | exact superpose eq126 eq10
    | (have j1 := eq126 X0 X1
       grind)
    | exact resolve eq10 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq633 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq614 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq614
    | (have j0 := eq614 X0 X1
       grind)
    | exact resolve eq614 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq641 : (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq593
    | exact resolve eq593 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq643 : (σ y) = (σ (M.op x y)) ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq21 eq591
    | exact resolve eq591 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq657 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq641
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq641
    | exact resolve eq641 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq659 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq643
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq643
    | exact resolve eq643 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq669 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq657
       have i₂ := eq75 x
       grind)
    | exact superpose eq75 eq657
    | exact resolve eq657 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq671 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq659
       have i₂ := eq75 sF0
       grind)
    | exact superpose eq75 eq659
    | exact resolve eq659 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq677 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq669
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq669
    | exact resolve eq669 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq679 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq21 eq671
    | exact resolve eq671 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq684 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq677
    | exact resolve eq677 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677
  have eq686 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ y)) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq679
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq679
    | exact resolve eq679 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq691 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq684
    | exact resolve eq684 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq693 : (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq686
       have i₂ := eq75 sF0
       grind)
    | exact superpose eq75 eq686
    | exact resolve eq686 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686
  have eq698 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq691
       have i₂ := eq75 x
       grind)
    | exact superpose eq75 eq691
    | exact resolve eq691 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq700 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq693
       have i₂ := eq9 (σ sF0) (σ sF0) (σ sF0)
       grind)
    | exact superpose eq9 eq693
    | exact resolve eq693 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq705 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq698
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq698
    | exact resolve eq698 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq707 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq700
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq700
    | exact resolve eq700 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq712 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq705
       have i₂ := eq9 sF2 sF2 sF2
       grind)
    | exact superpose eq9 eq705
    | exact resolve eq705 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq714 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21 eq707
    | exact resolve eq707 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq2662 : (σ (k y (M.op (M.op x y) (M.op x y)))) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq21 eq226
    | (have j0 := eq226 (M.op x y)
       grind)
    | exact resolve eq226 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq2671 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq407 eq2662
    | exact resolve eq2662 eq407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407 eq2662
  have eq2686 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq21 eq2671
    | exact resolve eq2671 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2671
  have eq7052 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq712 eq9
    | exact resolve eq9 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq7693 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq714 eq9
    | exact resolve eq9 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11751 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq7693 eq7052
    | exact resolve eq7052 eq7693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7693
  have eq11767 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq11751
    | exact resolve eq11751 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11751
  have eq11769 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq11767
       have r₂ := eq28
       grind)
    | exact resolve eq11767 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11767
  have eq11803 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq11769 eq395
    | exact resolve eq395 eq11769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11769
  have eq11810 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq11803
       have i₂ := eq60 sF1
       grind)
    | exact superpose eq60 eq11803
    | exact resolve eq11803 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11803
  have eq11878 : (τ (σ y)) = (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq11810 eq264
    | exact resolve eq264 eq11810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq11895 : (σ x) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq11810
  have eq11905 : (τ (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq40 eq11878
    | exact resolve eq11878 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11878
  have eq11920 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq42 eq11905
    | exact resolve eq11905 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11905
  have eq12040 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq11920 eq714
    | exact resolve eq714 eq11920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714 eq11920
  have eq12079 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq12040
  have eq12099 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq27 eq12079
    | exact resolve eq12079 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12079
  have eq12103 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq12099
       have r₂ := eq28
       grind)
    | exact resolve eq12099 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12099
  have eq12111 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq12103 eq75
    | exact resolve eq75 eq12103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12103
  have eq12137 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq12111
    | exact resolve eq12111 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12111
  have eq12140 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12137
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12137
    | exact resolve eq12137 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12137
  have eq12186 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq12140 eq7052
    | exact resolve eq7052 eq12140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12212 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq12186
  have eq12226 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq12212
    | exact resolve eq12212 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12212
  have eq12238 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq12226
       have r₂ := eq28
       grind)
    | exact resolve eq12226 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12226
  have eq12329 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq12238 eq395
    | exact resolve eq395 eq12238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12238
  have eq12336 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12329
       have i₂ := eq60 sF1
       grind)
    | exact superpose eq60 eq12329
    | exact resolve eq12329 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12329
  have eq12353 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq12336
       have r₂ := eq11895
       grind)
    | exact resolve eq12336 eq11895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11895 eq12336
  have eq12974 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq12353 eq12140
    | exact resolve eq12140 eq12353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12140
  have eq12975 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq12353 eq7052
    | exact resolve eq7052 eq12353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7052 eq12353
  have eq13001 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq12975
  have eq13002 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq12974
  have eq13028 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13002 eq27
    | exact resolve eq27 eq13002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13032 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13002 eq42
    | exact resolve eq42 eq13002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13002
  have eq13087 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq41 eq13032
    | exact resolve eq13032 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13032
  have eq13096 : y = (τ (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13087 eq42
    | exact resolve eq42 eq13087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13087
  have eq13142 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq40 eq13096
    | exact resolve eq13096 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13096
  have eq13150 : x = (τ (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq13142 eq41
    | exact resolve eq41 eq13142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13142
  have eq13197 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq40 eq13150
    | exact resolve eq13150 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13150
  have eq13402 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13028 eq13001
    | exact resolve eq13001 eq13028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13001 eq13028
  have eq13431 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq13402
  have eq13448 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq13431
       have r₂ := eq28
       grind)
    | exact resolve eq13431 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13431
  have eq13459 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13448 eq42
    | exact resolve eq42 eq13448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq13448
  have eq13505 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40 eq13459
    | exact resolve eq13459 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13459
  have eq13513 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13505 eq41
    | exact resolve eq41 eq13505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq13505
  have eq13560 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq40 eq13513
    | exact resolve eq13513 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq13513
  have eq13564 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13560 eq21
    | exact resolve eq21 eq13560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13566 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13560 eq56
    | exact resolve eq56 eq13560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq13590 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq13560
  have eq13591 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13564
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq13564
    | exact resolve eq13564 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13564
  have eq14479 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13566 (M.op y x)
       have i₂ := eq13566 x
       grind)
    | exact superpose eq13566 eq13566
    | exact resolve eq13566 eq13566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13566
  have eq14493 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq14479
  have eq14513 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75 y
       have i₂ := eq14493
       grind)
    | exact superpose eq14493 eq75
    | exact resolve eq75 eq14493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14493
  have eq14539 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14513
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14513
    | exact resolve eq14513 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14513
  have eq14542 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13591 eq14539
    | exact resolve eq14539 eq13591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13591 eq14539
  have eq14592 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq14542
  have eq14776 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq406
       have i₂ := eq633 sF0 (M.op x x)
       grind)
    | exact superpose eq633 eq406
    | (have j1 := eq633 (M.op x y) (M.op x x)
       grind)
    | exact resolve eq406 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406 eq633
  have eq14995 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq14776
       have i₂ := eq75 x
       grind)
    | exact superpose eq75 eq14776
    | exact resolve eq14776 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14776
  have eq15187 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq14995
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14995
    | exact resolve eq14995 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14995
  have eq15321 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq15187
    | exact resolve eq15187 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15187
  have eq15417 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (σ (M.op x x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq15321
    | exact resolve eq15321 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15321
  have eq15465 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15417
       have i₂ := eq75 x
       grind)
    | exact superpose eq75 eq15417
    | exact resolve eq15417 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15417
  have eq15506 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15465
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15465
    | exact resolve eq15465 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15465
  have eq15541 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15506
       have i₂ := eq9 sF2 sF2 sF2
       grind)
    | exact superpose eq9 eq15506
    | exact resolve eq15506 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15506
  have eq15653 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14592 eq2686
    | exact resolve eq2686 eq14592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2686 eq14592
  have eq15715 : (σ (M.op x y)) = (σ (k y (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq100 eq15653
    | exact resolve eq15653 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq15653
  have eq15842 : (σ (M.op x y)) = (σ (k y y)) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq13197 eq15715
    | exact resolve eq15715 eq13197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13197 eq15715
  have eq15886 : (σ (M.op x y)) = (σ (k y y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq15842
  have eq15917 : (σ (M.op x y)) = (σ (k y y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq15886
       have r₂ := eq13590
       grind)
    | exact resolve eq15886 eq13590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13590 eq15886
  have eq15919 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15917
       have i₂ := eq60 y
       grind)
    | exact superpose eq60 eq15917
    | exact resolve eq15917 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15917
  have eq15921 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15919
       have i₂ := eq75 y
       grind)
    | exact superpose eq75 eq15919
    | exact resolve eq15919 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15919
  have eq15923 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15921
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15921
    | exact resolve eq15921 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq15921
  have eq15961 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15923 eq30
    | exact resolve eq30 eq15923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq15923
  have eq31270 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15541 eq15961
    | exact resolve eq15961 eq15541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15541
  have eq31282 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq31270
  have eq31285 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq31282
    | exact resolve eq31282 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31282
  have eq31287 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq31285
       have r₂ := eq28
       grind)
    | exact resolve eq31285 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31285
  have eq31326 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31287 eq395
    | exact resolve eq395 eq31287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395 eq31287
  have eq31333 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq31326
       have i₂ := eq60 sF1
       grind)
    | exact superpose eq60 eq31326
    | exact resolve eq31326 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq31326
  have eq31450 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31333 eq15961
    | exact resolve eq15961 eq31333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15961 eq31333
  have eq31478 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq31450
  have eq31505 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq31478
    | exact resolve eq31478 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31478
  have eq31522 : x = (M.op x y) := by
    first
    | (have r₁ := eq31505
       have r₂ := eq28
       grind)
    | exact resolve eq31505 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31505
  have eq31524 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq31522 eq21
    | exact resolve eq21 eq31522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq31531 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq31522 eq55
    | exact resolve eq55 eq31522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq31533 : x ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq31522 eq58
    | exact resolve eq58 eq31522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq34636 : x = (k y x) ∨ x ≠ (M.op x x) := by
    first
    | exact superpose eq31522 eq31533
    | exact resolve eq31533 eq31522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31522 eq31533
  have eq34639 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq31524
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq31524
    | exact resolve eq31524 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31524
  have eq34924 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq34639 eq23
    | exact resolve eq23 eq34639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq34925 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq34639 eq27
    | exact resolve eq27 eq34639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq34938 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq34639 eq137
    | exact resolve eq137 eq34639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq36678 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (σ (k y x)) := by
    first
    | exact superpose eq34639 eq34938
    | exact resolve eq34938 eq34639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34639 eq34938
  have eq37152 : x = (M.op x x) := by
    first
    | (have i₁ := eq31531 (M.op x x)
       have i₂ := eq31531 x
       grind)
    | exact superpose eq31531 eq31531
    | exact resolve eq31531 eq31531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31531
  have eq37293 : x ≠ x ∨ x = (k y x) := by
    first
    | (have i₁ := eq34636
       have i₂ := eq37152
       grind)
    | exact superpose eq37152 eq34636
    | (have r₁ := eq34636
       have r₂ := eq37152
       grind)
    | exact resolve eq34636 eq37152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34636
  have eq37312 : x = (k y x) := by grind
  clear eq37293
  have eq37351 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq36678
       have i₂ := eq37312
       grind)
    | exact superpose eq37312 eq36678
    | exact resolve eq36678 eq37312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36678 eq37312
  have eq37376 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq37351
       have i₂ := eq34924
       grind)
    | exact superpose eq34924 eq37351
    | exact resolve eq37351 eq34924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37351
  have eq37377 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq37376
  have eq37522 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq75 x
       have i₂ := eq37152
       grind)
    | exact superpose eq37152 eq75
    | exact resolve eq75 eq37152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq37152
  have eq37572 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq37522
       have i₂ := eq34924
       grind)
    | exact superpose eq34924 eq37522
    | exact resolve eq37522 eq34924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34924 eq37522
  have eq37725 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq37572 eq37377
    | exact resolve eq37377 eq37572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37377
  have eq37738 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq37725
       have r₂ := eq28
       grind)
    | exact resolve eq37725 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37725
  have eq38680 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq37738 eq34925
    | exact resolve eq34925 eq37738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34925 eq37738
  have eq38708 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37572 eq38680
    | exact resolve eq38680 eq37572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37572 eq38680
  have eq39151 : False := by grind
  exact eq39151

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_x_y_pyx_Equation2146 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq85 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq163 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq85 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq85
    | exact resolve eq85 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq16 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
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
  have eq178 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op (M.op X3 X3) X2) X1 (M.op X0 X2)
       have i₂ := eq16 X0 X3 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 : G, (M.op (M.op X1 X1) y) = (M.op (M.op (M.op X0 X0) (M.op x y)) x) := by
    intro X0 X1
    first
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq337 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
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
  have eq365 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq337 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq337
    | exact resolve eq337 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq407 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq561 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq407 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq174 (σ X0)
       grind)
    | exact superpose eq174 eq407
    | exact resolve eq407 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq590 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq561 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq561
    | exact resolve eq561 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq701 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq176 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq176 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq176 eq176
    | exact resolve eq176 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq703 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) X0) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 X1 (M.op X0 (M.op X2 (M.op X3 X3)))
       have i₂ := eq176 X2 X3 X0
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq730 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X2 ∨ (k X1 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq701 X0 X1
       grind)
    | (have i₁ := eq13 X1 X2
       have i₂ := eq701 X1 X0
       grind)
    | exact superpose eq701 eq13
    | (have j0 := eq13 X0 X2
       grind)
    | (have r₁ := eq13 X1 (M.op X0 X0)
       have r₂ := eq701 X0 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq701 X0 X1
       grind)
    | exact resolve eq13 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq732 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq174 X1
       have i₂ := eq701 X0 X1
       grind)
    | (have i₁ := eq174 X1
       have i₂ := eq701 X1 X0
       grind)
    | exact superpose eq701 eq174
    | exact resolve eq174 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq736 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq701 X0 X2
       grind)
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq701 X2 X0
       grind)
    | exact superpose eq701 eq16
    | exact resolve eq16 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq741 : ∀ X0 X1 : G, (k X1 (τ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq590 X1
       have i₂ := eq701 X0 (σ X1)
       grind)
    | (have i₁ := eq590 X1
       have i₂ := eq701 (σ X1) X0
       grind)
    | exact superpose eq701 eq590
    | exact resolve eq590 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq742 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq365 X1
       have i₂ := eq701 X0 (τ X1)
       grind)
    | (have i₁ := eq365 X1
       have i₂ := eq701 (τ X1) X0
       grind)
    | exact superpose eq701 eq365
    | exact resolve eq365 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq775 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (σ (M.op X1 X1))
       have i₂ := eq742 X1 (τ X0)
       grind)
    | exact superpose eq742 eq34
    | exact resolve eq34 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq794 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq775 X0 X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq775
    | exact resolve eq775 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq821 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) ≠ X0 ∨ (M.op (M.op X1 X1) X2) = (M.op (M.op X0 X2) (M.op X0 X2)) ∨ (M.op (M.op X1 X1) X2) = (k (M.op X0 X2) (M.op (M.op X1 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 X2) (M.op (M.op X1 X1) X2)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq12
    | (have j0 := eq12 (M.op X0 X2) (M.op (M.op X1 X1) X2)
       grind)
    | (have r₁ := eq12 (M.op (M.op (M.op X1 X1) X2) X2) (M.op (M.op X1 X1) X2)
       have r₂ := eq16 (M.op (M.op X1 X1) X2) X1 X2
       grind)
    | exact resolve eq12 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq824 : x ≠ (M.op x y) ∨ x = (M.op y y) ∨ x = (k y x) := by
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
  have eq825 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq828 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X1
       have i₂ := eq701 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq701 X0 X1
       grind)
    | exact superpose eq701 eq11
    | (have j0 := eq11 X0 (k X1 X1)
       grind)
    | exact resolve eq11 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq829 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X1) = (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op (M.op X2 X2) X1) = X0 ∨ (k (M.op X0 X1) (M.op (M.op X2 X2) X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (M.op X0 X2) (M.op (M.op X1 X1) X2)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq11
    | (have j0 := eq11 (M.op X0 X1) (M.op (M.op X2 X2) X1)
       grind)
    | exact resolve eq11 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq832 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq833 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq841 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq701 X0 X1
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq701
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq701 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq847 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X2) X0) (k X0 X1)) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq867 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq868 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq869 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq868 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq883 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq841 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841
  have eq891 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq828 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq1422 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X0) = (M.op (M.op X2 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 (M.op X1 X1) X1 (M.op (M.op X2 X2) X0)
       have i₂ := eq736 (M.op X1 X1) X2 X0
       grind)
    | exact superpose eq736 eq176
    | exact resolve eq176 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2284 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq869 X1
       have i₂ := eq883 X1 X0
       grind)
    | exact superpose eq883 eq869
    | (have j0 := eq869 X1
       have j1 := eq883 X1 X1
       grind)
    | (have r₁ := eq869 (M.op X1 X1)
       have r₂ := eq883 (M.op X1 X1) X1
       grind)
    | exact resolve eq869 eq883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869 eq883
  have eq2302 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2284 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2284
  have eq2360 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq701 X2 X1
       have i₂ := eq891 X2 X0
       grind)
    | exact superpose eq891 eq701
    | (have j1 := eq891 X1 X0
       grind)
    | exact resolve eq701 eq891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2446 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq742 X1 (σ (M.op X1 X1))
       have i₂ := eq891 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq891 eq742
    | (have j1 := eq891 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq742 eq891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq2447 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (M.op X1 X1))) ∨ (M.op X0 X0) = (σ (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq794 (σ (σ (M.op X1 X1))) X1
       have i₂ := eq891 X0 (σ (σ (M.op X1 X1)))
       grind)
    | exact superpose eq891 eq794
    | (have j1 := eq891 X0 (σ (σ (M.op X1 X1)))
       grind)
    | exact resolve eq794 eq891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794
  have eq2451 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq741 X1 (τ (M.op X1 X1))
       have i₂ := eq891 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq891 eq741
    | (have j1 := eq891 X0 (τ (M.op X1 X1))
       grind)
    | exact resolve eq741 eq891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2459 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq891 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891
  have eq2463 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2451 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2451
  have eq2466 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq2447 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2447
  have eq2467 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2446 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2446
  have eq2491 : ∀ X0 X2 : G, (σ (M.op X0 X0)) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq2467 x X2
       have i₂ := eq2467 x X0
       grind)
    | exact superpose eq2467 eq2467
    | exact resolve eq2467 eq2467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2518 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (σ (M.op (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2467 X2 (M.op X1 X1)
       have i₂ := eq1422 (M.op X1 X1) X1 X0
       grind)
    | (have i₁ := eq2467 X2 (M.op X1 X1)
       have i₂ := eq1422 (M.op X1 X1) X0 X1
       grind)
    | exact superpose eq1422 eq2467
    | exact resolve eq2467 eq1422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2521 : ∀ X0 X2 X3 : G, (M.op (M.op (σ (M.op X0 X0)) X2) (M.op X3 X2)) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq16 X3 x X2
       have i₂ := eq2467 x X0
       grind)
    | exact superpose eq2467 eq16
    | exact resolve eq16 eq2467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2523 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X1 (σ (M.op X0 X0))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X1 x X2
       have i₂ := eq2467 x X0
       grind)
    | exact superpose eq2467 eq176
    | exact resolve eq176 eq2467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2525 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op X0 X0)) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq178 x
       have i₂ := eq2467 x X0
       grind)
    | exact superpose eq2467 eq178
    | exact resolve eq178 eq2467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2584 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (σ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 (M.op X1 X1) X1 X2
       have i₂ := eq2467 (M.op X1 X1) X0
       grind)
    | exact superpose eq2467 eq176
    | exact resolve eq176 eq2467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2632 : ∀ X0 X1 : G, (k (M.op X1 X1) x) = (τ (k (M.op X0 X0) (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq59 (M.op X1 X1)
       have i₂ := eq2467 X0 X1
       grind)
    | exact superpose eq2467 eq59
    | exact resolve eq59 eq2467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2634 : ∀ X0 X1 : G, (k (M.op X1 X1) (M.op x y)) = (τ (k (M.op X0 X0) (σ (M.op x y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq85 (M.op X1 X1)
       have i₂ := eq2467 X0 X1
       grind)
    | exact superpose eq2467 eq85
    | exact resolve eq85 eq2467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq2642 : ∀ X0 X1 : G, (k (M.op X1 X1) (M.op x y)) = (k (τ (M.op X0 X0)) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq163 eq2634
    | exact resolve eq2634 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq2634
  have eq2644 : ∀ X0 X1 : G, (k (M.op X1 X1) x) = (k (τ (M.op X0 X0)) x) := by
    intro X0 X1
    first
    | exact superpose eq141 eq2632
    | exact resolve eq2632 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq2632
  have eq2706 : ∀ X0 X2 X3 : G, (M.op (M.op (τ (M.op X0 X0)) X2) (M.op X3 X2)) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq16 X3 x X2
       have i₂ := eq2463 x X0
       grind)
    | exact superpose eq2463 eq16
    | exact resolve eq16 eq2463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2764 : ∀ X0 X2 : G, (τ (M.op X0 X0)) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq2467 x X2
       have i₂ := eq2463 x X0
       grind)
    | exact superpose eq2463 eq2467
    | exact resolve eq2467 eq2463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2771 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (τ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 (M.op X1 X1) X1 X2
       have i₂ := eq2463 (M.op X1 X1) X0
       grind)
    | exact superpose eq2463 eq176
    | exact resolve eq176 eq2463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2780 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (τ (M.op X0 X0)) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq736 X2 X1 (M.op X1 X1)
       have i₂ := eq2463 (M.op X1 X1) X0
       grind)
    | exact superpose eq2463 eq736
    | exact resolve eq736 eq2463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2943 : ∀ X0 X2 : G, (σ (M.op X2 X2)) = (σ (σ (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq2467 x X2
       have i₂ := eq2466 x X0
       grind)
    | exact superpose eq2466 eq2467
    | exact resolve eq2467 eq2466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2466 eq2467
  have eq3143 : ∀ X0 X1 : G, (k (M.op X1 X1) x) = (τ (k (σ (M.op X0 X0)) (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq59 (M.op X1 X1)
       have i₂ := eq2491 X1 X0
       grind)
    | (have i₁ := eq59 (M.op X1 X1)
       have i₂ := eq2491 X0 X1
       grind)
    | exact superpose eq2491 eq59
    | exact resolve eq59 eq2491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2491
  have eq3155 : ∀ X0 X1 : G, (k (M.op X1 X1) x) = (k (M.op X0 X0) x) := by
    intro X0 X1
    first
    | exact superpose eq59 eq3143
    | exact resolve eq3143 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq3143
  have eq3976 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq832
       grind)
    | exact superpose eq832 eq39
    | exact resolve eq39 eq832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3977 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3976
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3976
    | exact resolve eq3976 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3976
  have eq3979 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq3977
    | exact resolve eq3977 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3977
  have eq4442 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) = (M.op (M.op (M.op X4 X4) X0) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq179 X2 X4 (M.op X0 (M.op X2 (M.op X3 X3))) X1
       have i₂ := eq176 X2 X3 X0
       grind)
    | exact superpose eq176 eq179
    | exact resolve eq179 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq4464 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op x y)) = (M.op (M.op (M.op X1 X1) x) (M.op (M.op X2 X2) y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq177 eq179
    | exact resolve eq179 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4507 : ∀ X0 X1 X2 X4 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X1) (M.op X4 X2)) = X4 := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq16 X4 x X2
       have i₂ := eq179 X1 X0 X2 x
       grind)
    | (have i₁ := eq16 X0 (M.op X2 X2) X2
       have i₂ := eq179 X2 X2 X2 x
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4513 : ∀ X0 X1 : G, x = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 y)) X1) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq177 x
       have i₂ := eq179 X1 X0 y x
       grind)
    | (have i₁ := eq177 (M.op y y)
       have i₂ := eq179 y y y x
       grind)
    | exact superpose eq179 eq177
    | exact resolve eq177 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq4514 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 (σ y))) X1) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq178 x
       have i₂ := eq179 X0 X1 sF3 x
       grind)
    | (have i₁ := eq178 (M.op sF3 sF3)
       have i₂ := eq179 sF3 sF3 sF3 x
       grind)
    | exact superpose eq179 eq178
    | exact resolve eq178 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq12852 : ∀ X0 X1 : G, (σ (k (M.op X0 X0) (M.op x y))) = (k (σ (τ (M.op X1 X1))) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq2642 eq41
    | exact resolve eq41 eq2642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2642
  have eq12857 : ∀ X0 X1 : G, (σ (k (M.op X0 X0) (M.op x y))) = (k (M.op X1 X1) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq12852 X0 X1
       have i₂ := eq14 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq12852
    | exact resolve eq12852 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12852
  have eq12872 : ∀ X0 X1 : G, (k (σ (M.op X0 X0)) (σ (M.op x y))) = (k (M.op X1 X1) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq41 eq12857
    | exact resolve eq12857 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12857
  have eq19874 : ∀ X0 X2 : G, (k (M.op X0 X0) (σ (M.op x y))) = (k (M.op X2 X2) (σ (M.op x y))) := by
    intro X0 X2
    first
    | exact superpose eq12872 eq12872
    | exact resolve eq12872 eq12872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12872
  have eq27942 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3979 eq833
    | exact resolve eq833 eq3979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3979
  have eq27953 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq27942
       have r₂ := eq27
       grind)
    | exact resolve eq27942 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27942
  have eq28132 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq27953 eq741
    | exact resolve eq741 eq27953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq28254 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (τ (σ x)) (M.op X1 X1)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq27953 eq2780
    | exact resolve eq2780 eq27953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2780 eq27953
  have eq28388 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op x (M.op X1 X1)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq29 eq28254
    | exact resolve eq28254 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28254
  have eq28479 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq29 eq28132
    | exact resolve eq28132 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28132
  have eq28526 : ∀ X0 : G, (M.op X0 X0) = (M.op x (k x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq2360 eq28388
    | (have j1 := eq2360 (M.op x (k x x)) x X0
       grind)
    | exact resolve eq28388 eq2360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28388
  have eq28581 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq28479 X0
       have j1 := eq730 X0 X0 x
       grind)
    | (have r₁ := eq28479 (M.op X0 X0)
       have r₂ := eq730 X0 x (k (M.op X0 X0) x)
       grind)
    | (have r₁ := eq28479 X0
       have r₂ := eq730 y x x
       grind)
    | exact resolve eq28479 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28479
  have eq28606 : (k x x) = (M.op x (k x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2360 eq28526
    | (have j1 := eq2360 x x y
       grind)
    | exact resolve eq28526 eq2360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28526
  have eq28663 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28581 eq28606
    | exact resolve eq28606 eq28581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28606
  have eq28710 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq2302 x x
       grind)
    | (have r₁ := eq28663
       have r₂ := eq2302 x x
       grind)
    | (have r₁ := eq28663
       have r₂ := eq2302 y x
       grind)
    | exact resolve eq28663 eq2302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28663
  have eq28789 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = x ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2459 X0 x
       have i₂ := eq28581 x
       grind)
    | exact superpose eq28581 eq2459
    | (have j0 := eq2459 X0 x
       grind)
    | (have r₁ := eq2459 X0 x
       have r₂ := eq28581 x
       grind)
    | exact resolve eq2459 eq28581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2459
  have eq28798 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq34 X0 x
       have i₂ := eq28581 (τ X0)
       grind)
    | exact superpose eq28581 eq34
    | exact resolve eq34 eq28581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq28801 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq28581 x
       grind)
    | exact superpose eq28581 eq35
    | exact resolve eq35 eq28581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq28802 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq832
       have i₂ := eq28581 y
       grind)
    | exact superpose eq28581 eq832
    | exact resolve eq832 eq28581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28581
  have eq28808 : x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq28802
  have eq28809 : ∀ X0 : G, (M.op X0 X0) = x ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq28789 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28789
  have eq28817 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28801
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28801
    | exact resolve eq28801 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28801
  have eq28818 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq28798 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28798
    | (have j0 := eq28798 X0
       grind)
    | exact resolve eq28798 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28798
  have eq28824 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq28818 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq28818
    | exact resolve eq28818 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28818
  have eq28911 : ∀ X1 X2 : G, (M.op (M.op x X1) (M.op X2 X1)) = X2 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X1 X2
    first
    | (have i₁ := eq16 X2 x X1
       have i₂ := eq28809 x
       grind)
    | exact superpose eq28809 eq16
    | exact resolve eq16 eq28809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28917 : ∀ X1 X2 X3 : G, (M.op (M.op (M.op X2 X2) (M.op X3 X1)) X3) = (M.op x X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq179 X3 X2 X1 x
       have i₂ := eq28809 x
       grind)
    | exact superpose eq28809 eq179
    | exact resolve eq179 eq28809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq28990 : ∀ X1 X2 : G, x = (k X1 X1) ∨ (M.op X2 X2) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X1 X2
    first
    | (have i₁ := eq2360 X1 x X2
       have i₂ := eq28809 x
       grind)
    | exact superpose eq28809 eq2360
    | (have j0 := eq2360 X1 X1 X2
       grind)
    | exact resolve eq2360 eq28809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29013 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 (σ x)))) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq2523 x X0 X1
       have i₂ := eq28809 x
       grind)
    | exact superpose eq28809 eq2523
    | exact resolve eq2523 eq28809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29054 : ∀ X1 X2 : G, (M.op (M.op (τ x) X1) (M.op X2 X1)) = X2 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X1 X2
    first
    | (have i₁ := eq2706 x X1 X2
       have i₂ := eq28809 x
       grind)
    | exact superpose eq28809 eq2706
    | exact resolve eq2706 eq28809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29096 : ∀ X1 : G, (σ x) = (σ (σ (M.op X1 X1))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq2943 X1 x
       have i₂ := eq28809 x
       grind)
    | exact superpose eq28809 eq2943
    | exact resolve eq2943 eq28809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2943
  have eq29177 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) x) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X1
       have i₂ := eq28809 X1
       grind)
    | exact superpose eq28809 eq16
    | exact resolve eq16 eq28809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29181 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 X0)) X1) x) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq2521 X0 X1 X1
       have i₂ := eq28809 X1
       grind)
    | exact superpose eq28809 eq2521
    | exact resolve eq2521 eq28809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2521
  have eq29196 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (M.op X1 x)) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq2523 X0 (σ (M.op X0 X0)) X1
       have i₂ := eq28809 (σ (M.op X0 X0))
       grind)
    | exact superpose eq28809 eq2523
    | exact resolve eq2523 eq28809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2523
  have eq29205 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2518 x x X0
       have i₂ := eq28809 (M.op x x)
       grind)
    | exact superpose eq28809 eq2518
    | exact resolve eq2518 eq28809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2518
  have eq29219 : ∀ X0 : G, x = (σ (M.op X0 X0)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2584 X0 (σ (M.op X0 X0)) (σ (M.op X0 X0))
       have i₂ := eq28809 (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))
       grind)
    | exact superpose eq28809 eq2584
    | exact resolve eq2584 eq28809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2584
  have eq29220 : ∀ X0 : G, x = (τ (M.op X0 X0)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2771 X0 (τ (M.op X0 X0)) (τ (M.op X0 X0))
       have i₂ := eq28809 (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))
       grind)
    | exact superpose eq28809 eq2771
    | exact resolve eq2771 eq28809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2771
  have eq29284 : x = (τ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28809 eq29220
    | exact resolve eq29220 eq28809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29220
  have eq29285 : x = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28809 eq29219
    | exact resolve eq29219 eq28809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29219
  have eq29294 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq29205 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29205
    | (have j0 := eq29205 X0
       grind)
    | exact resolve eq29205 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29205
  have eq29300 : ∀ X1 : G, (M.op (σ x) (M.op X1 x)) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq28809 eq29196
    | exact resolve eq29196 eq28809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29196
  have eq29314 : ∀ X1 : G, (M.op (M.op (σ x) X1) x) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq28809 eq29181
    | exact resolve eq29181 eq28809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29181
  have eq29318 : ∀ X1 : G, (M.op (M.op x X1) x) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq28809 eq29177
    | exact resolve eq29177 eq28809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29177
  have eq29376 : ∀ X1 : G, (σ x) = (σ (σ (M.op X1 X1))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq29096 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29096
    | (have j0 := eq29096 X1
       grind)
    | exact resolve eq29096 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29096
  have eq29451 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 (σ x)))) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq29013 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29013
    | (have j0 := eq29013 X0 X1
       grind)
    | exact resolve eq29013 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29013
  have eq29514 : ∀ X1 X3 : G, (M.op x X1) = (M.op (M.op x (M.op X3 X1)) X3) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X1 X3
    first
    | exact superpose eq28809 eq28917
    | exact resolve eq28917 eq28809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28917
  have eq29567 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29285
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29285
    | exact resolve eq29285 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29285
  have eq29574 : ∀ X1 : G, (M.op (σ x) (M.op X1 x)) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq29300 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29300
    | (have j0 := eq29300 X1
       grind)
    | exact resolve eq29300 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29300
  have eq29584 : ∀ X1 : G, (M.op (M.op (σ x) X1) x) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq29314 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29314
    | (have j0 := eq29314 X1
       grind)
    | exact resolve eq29314 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29314
  have eq29636 : (σ x) = (σ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28809 eq29376
    | exact resolve eq29376 eq28809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29376
  have eq29748 : ∀ X1 : G, (M.op (σ x) (M.op X1 (σ x))) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq29567 eq29574
    | exact resolve eq29574 eq29567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29574
  have eq29754 : ∀ X1 : G, (M.op (M.op (σ x) X1) (σ x)) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq29567 eq29584
    | exact resolve eq29584 eq29567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29584
  have eq29794 : (σ x) = (σ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29636
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29636
    | exact resolve eq29636 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29636
  have eq29945 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29567 eq825
    | (have r₁ := eq825
       have r₂ := eq29567
       grind)
    | exact resolve eq825 eq29567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29952 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (σ x) ∨ x = (M.op x y) := by grind
  clear eq29945
  have eq30723 : ∀ X1 : G, (M.op (M.op (M.op X1 X1) (M.op x y)) x) = (M.op (σ x) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq195 X1 x
       have i₂ := eq29294 x
       grind)
    | exact superpose eq29294 eq195
    | exact resolve eq195 eq29294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29294
  have eq31351 : (M.op (σ x) y) = (M.op (M.op x (M.op x y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28809 eq30723
    | exact resolve eq30723 eq28809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30723
  have eq31587 : (M.op x y) = (M.op (σ x) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29318 eq31351
    | exact resolve eq31351 eq29318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31351
  have eq34241 : ∀ X0 : G, (M.op (M.op X0 X0) y) = (M.op x x) ∨ y = (M.op (M.op X0 X0) y) ∨ y = (k x (M.op (M.op X0 X0) y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq829 y y x
       have i₂ := eq28808
       grind)
    | exact superpose eq28808 eq829
    | (have j0 := eq829 (M.op x x) y X0
       grind)
    | exact resolve eq829 eq28808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829 eq28808
  have eq34252 : ∀ X0 : G, x = (M.op (M.op X0 X0) y) ∨ y = (M.op (M.op X0 X0) y) ∨ y = (k x (M.op (M.op X0 X0) y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq28710 eq34241
    | (have j0 := eq34241 X0
       grind)
    | exact resolve eq34241 eq28710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28710 eq34241
  have eq34401 : ∀ X0 : G, x = (M.op x y) ∨ y = (M.op (M.op X0 X0) y) ∨ y = (k x (M.op (M.op X0 X0) y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq28809 eq34252
    | (have j0 := eq34252 X0
       grind)
    | exact resolve eq34252 eq28809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34252
  have eq34477 : ∀ X0 : G, x = (M.op x y) ∨ y = (M.op (M.op X0 X0) y) ∨ y = (k x (M.op (M.op X0 X0) y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq34401 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq34401
    | (have j0 := eq34401 X0
       grind)
    | exact resolve eq34401 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34401
  have eq34478 : ∀ X0 : G, x = (M.op x y) ∨ y = (M.op (M.op X0 X0) y) ∨ y = (k x (M.op (M.op X0 X0) y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq34477 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34477
  have eq34525 : ∀ X0 : G, x = (M.op x y) ∨ y = (M.op x y) ∨ y = (k x (M.op (M.op X0 X0) y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq28809 eq34478
    | (have j0 := eq34478 X0
       grind)
    | exact resolve eq34478 eq28809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34478
  have eq34546 : ∀ X0 : G, y = (M.op x y) ∨ x = (M.op x y) ∨ y = (k x (M.op (M.op X0 X0) y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq34525 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq34525
    | (have j0 := eq34525 X0
       grind)
    | exact resolve eq34525 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34525
  have eq34547 : ∀ X0 : G, y = (M.op x y) ∨ x = (M.op x y) ∨ y = (k x (M.op (M.op X0 X0) y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq34546 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34546
  have eq34555 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (k x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28809 eq34547
    | exact resolve eq34547 eq28809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34547
  have eq34559 : y = (k x (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq34555
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq34555
    | exact resolve eq34555 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34555
  have eq34561 : y = (k (σ x) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29567 eq34559
    | exact resolve eq34559 eq29567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34559
  have eq36109 : (σ y) = (k (σ (σ x)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34561 eq41
    | exact resolve eq41 eq34561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34561
  have eq36113 : (σ y) = (k (σ (σ x)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq36109
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36109
    | exact resolve eq36109 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36109
  have eq36116 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29794 eq36113
    | exact resolve eq36113 eq29794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29794 eq36113
  have eq36539 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op X0 X0) (σ x)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq36116 eq847
    | (have j0 := eq847 (σ x) (σ (M.op x y)) x
       grind)
    | exact resolve eq847 eq36116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq36542 : (σ (M.op x y)) = (M.op (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ x)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2360 eq36539
    | (have j1 := eq2360 (σ (M.op x y)) x (σ x)
       grind)
    | exact resolve eq36539 eq2360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2360 eq36539
  have eq36547 : (σ (M.op x y)) = (M.op (M.op x (σ x)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28990 eq36542
    | (have j1 := eq28990 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq36542 eq28990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28990 eq36542
  have eq36551 : (σ (M.op x y)) = (M.op (M.op x (σ x)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28809 eq36547
    | exact resolve eq36547 eq28809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36547
  have eq36554 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29567 eq36551
    | exact resolve eq36551 eq29567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36551
  have eq36555 : (σ (M.op x y)) = (M.op x (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28809 eq36554
    | exact resolve eq36554 eq28809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36554
  have eq36556 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29567 eq36555
    | exact resolve eq36555 eq29567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36555
  have eq36557 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq36556
    | exact resolve eq36556 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36556
  have eq36558 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq36557
       have r₂ := eq27
       grind)
    | exact resolve eq36557 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36557
  have eq36559 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29567 eq36558
    | exact resolve eq36558 eq29567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36558
  have eq38265 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X1 y)) X1) = (M.op (M.op x (M.op x y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq4513 eq28911
    | exact resolve eq28911 eq4513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4513 eq28911
  have eq38991 : ∀ X1 : G, (M.op (M.op x (M.op x y)) x) = (M.op (M.op x (M.op X1 y)) X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq28809 eq38265
    | exact resolve eq38265 eq28809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38265
  have eq39252 : ∀ X1 : G, (M.op x y) = (M.op (M.op x (M.op X1 y)) X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq29318 eq38991
    | exact resolve eq38991 eq29318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29318 eq38991
  have eq39439 : ∀ X1 : G, (M.op x y) = (M.op (M.op (σ x) (M.op X1 y)) X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq29567 eq39252
    | exact resolve eq39252 eq29567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39252
  have eq45018 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (σ x) (M.op (M.op X0 (σ x)) y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq39439 eq29451
    | exact resolve eq29451 eq39439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29451
  have eq45043 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (σ x) (M.op (M.op X0 (σ x)) y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq45018 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45018
  have eq57250 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29952 eq107
    | exact resolve eq107 eq29952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq29952
  have eq57268 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (k y x) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq57250
    | exact resolve eq57250 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57250
  have eq59243 : ∀ X0 : G, x = (k y x) ∨ (M.op X0 X0) = (σ x) ∨ x = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq57268 eq701
    | exact resolve eq701 eq57268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59311 : ∀ X0 : G, (M.op X0 X0) = (τ (σ x)) ∨ x = (k y x) ∨ x = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq57268 eq2463
    | exact resolve eq2463 eq57268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2463 eq57268
  have eq59563 : ∀ X0 : G, (M.op X0 X0) = x ∨ x = (k y x) ∨ x = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq59311
    | exact resolve eq59311 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59311
  have eq59663 : x = (σ x) ∨ x = (k y x) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq59243 eq59563
    | exact resolve eq59563 eq59243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59243 eq59563
  have eq59664 : x = (k y x) ∨ x = (σ x) ∨ x = (M.op x y) := by grind
  clear eq59663
  have eq59712 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq832
       have i₂ := eq59664
       grind)
    | exact superpose eq59664 eq832
    | exact resolve eq832 eq59664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59664
  have eq59720 : x = (M.op y y) ∨ x = (M.op x y) ∨ x = (σ x) := by grind
  clear eq59712
  have eq59755 : ∀ X0 : G, (M.op X0 X0) = x ∨ x = (M.op x y) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq701 y X0
       have i₂ := eq59720
       grind)
    | exact superpose eq59720 eq701
    | exact resolve eq701 eq59720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59759 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x y) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq732 y X0
       have i₂ := eq59720
       grind)
    | exact superpose eq59720 eq732
    | exact resolve eq732 eq59720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59860 : ∀ X0 : G, (k (M.op X0 X0) x) = (k (τ x) x) ∨ x = (M.op x y) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq2644 y X0
       have i₂ := eq59720
       grind)
    | exact superpose eq59720 eq2644
    | exact resolve eq2644 eq59720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2644
  have eq59878 : ∀ X0 : G, (σ x) = (τ (M.op X0 X0)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq2764 X0 y
       have i₂ := eq59720
       grind)
    | exact superpose eq59720 eq2764
    | exact resolve eq2764 eq59720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2764
  have eq59906 : ∀ X0 : G, (k x x) = (k (M.op X0 X0) x) ∨ x = (M.op x y) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq3155 y X0
       have i₂ := eq59720
       grind)
    | exact superpose eq59720 eq3155
    | exact resolve eq3155 eq59720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3155 eq59720
  have eq60034 : ∀ X0 : G, (σ x) = (τ (M.op X0 X0)) ∨ x = (M.op x y) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq59878 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq59878
    | (have j0 := eq59878 X0
       grind)
    | exact resolve eq59878 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59878
  have eq60043 : (k x x) = (k (τ x) x) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq59906 eq59860
    | exact resolve eq59860 eq59906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59860 eq59906
  have eq60153 : (σ x) = (τ x) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq59755 eq60034
    | exact resolve eq60034 eq59755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59755 eq60034
  have eq60156 : (k x x) = (τ x) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq59759 eq60043
    | exact resolve eq60043 eq59759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60043
  have eq60207 : x = (τ x) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq59759 eq60156
    | exact resolve eq60156 eq59759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59759 eq60156
  have eq60235 : x = (σ x) ∨ x = (M.op x y) ∨ x = (σ x) := by
    first
    | exact superpose eq60153 eq60207
    | exact resolve eq60207 eq60153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60153 eq60207
  have eq60236 : x = (σ x) ∨ x = (M.op x y) := by grind
  clear eq60235
  have eq60252 : (M.op x y) = (M.op (σ x) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq60236
       grind)
    | exact superpose eq60236 eq18
    | exact resolve eq18 eq60236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60255 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq60236
       grind)
    | exact superpose eq60236 eq39
    | exact resolve eq39 eq60236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq60263 : (M.op x y) = (k y (σ x)) ∨ (M.op x y) = (σ x) ∨ (σ x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq832
       have i₂ := eq60236
       grind)
    | exact superpose eq60236 eq832
    | exact resolve eq832 eq60236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832
  have eq60322 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) := by grind
  have eq60363 : (σ x) = (M.op y y) ∨ (M.op x y) = (k y (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq60263
       have r₂ := eq60322
       grind)
    | exact resolve eq60263 eq60322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60263
  have eq65919 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) (M.op X1 X0)) = X1 ∨ (M.op x y) = (k y (σ x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 y X0
       have i₂ := eq60363
       grind)
    | exact superpose eq60363 eq16
    | exact resolve eq16 eq60363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65929 : ∀ X0 : G, (M.op x y) = (k y (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq701 y X0
       have i₂ := eq60363
       grind)
    | exact superpose eq60363 eq701
    | exact resolve eq701 eq60363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq65933 : ∀ X0 : G, (M.op x y) = (k y (σ x)) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq732 y X0
       have i₂ := eq60363
       grind)
    | exact superpose eq60363 eq732
    | exact resolve eq732 eq60363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq65935 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (σ x)) = X1 ∨ (M.op x y) = (k y (σ x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq736 y X0 X1
       have i₂ := eq60363
       grind)
    | exact superpose eq60363 eq736
    | exact resolve eq736 eq60363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65983 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (σ x) X1) ∨ (M.op x y) = (k y (σ x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1422 X1 X0 y
       have i₂ := eq60363
       grind)
    | exact superpose eq60363 eq1422
    | exact resolve eq1422 eq60363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1422
  have eq66117 : ∀ X0 : G, (k (σ x) (σ (M.op x y))) = (k (M.op X0 X0) (σ (M.op x y))) ∨ (M.op x y) = (k y (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq19874 X0 y
       have i₂ := eq60363
       grind)
    | exact superpose eq60363 eq19874
    | exact resolve eq19874 eq60363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19874 eq60363
  have eq66335 : ∀ X1 : G, (M.op (M.op (σ x) X1) (σ x)) = X1 ∨ (M.op x y) = (k y (σ x)) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq65983 eq65935
    | exact resolve eq65935 eq65983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65935 eq65983
  have eq66729 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq60255 X0
       have i₂ := eq65933 (k X0 sF2)
       grind)
    | exact superpose eq65933 eq60255
    | (have j1 := eq65933 X0
       grind)
    | exact resolve eq60255 eq65933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60255 eq65933
  have eq66738 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq66729 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66729
  have eq66743 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq66738 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq66738
    | (have j0 := eq66738 X0
       grind)
    | exact resolve eq66738 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66738
  have eq66746 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq66743
    | (have j0 := eq66743 X0
       grind)
    | exact resolve eq66743 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66743
  have eq66808 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have j0 := eq66746 (σ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75985 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op x y) = (k y (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq66335
    | (have j0 := eq66335 (σ y)
       grind)
    | exact resolve eq66335 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108649 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36559 eq12
    | (have j0 := eq12 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq12 (σ x) (σ (M.op x y))
       have r₂ := eq36559
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq36559
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq36559
       grind)
    | exact resolve eq12 eq36559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108657 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 (σ x))) X1) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq36559 eq4507
    | exact resolve eq4507 eq36559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36559
  have eq108674 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq108649
  have eq108687 : ∀ X1 : G, (σ (M.op x y)) = (M.op (M.op (M.op x (M.op X1 (σ x))) X1) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq28809 eq108657
    | exact resolve eq108657 eq28809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108657
  have eq108695 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36116 eq108674
    | exact resolve eq108674 eq36116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108674
  have eq108705 : (σ (M.op x y)) = (M.op (M.op x (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29514 eq108687
    | exact resolve eq108687 eq29514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29514 eq108687
  have eq108713 : x = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28809 eq108695
    | exact resolve eq108695 eq28809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108695
  have eq108719 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29567 eq108705
    | exact resolve eq108705 eq29567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108705
  have eq108727 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29567 eq108713
    | exact resolve eq108713 eq29567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108713
  have eq108728 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq108727
  have eq108732 : (σ (M.op x y)) = (M.op x (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28809 eq108719
    | exact resolve eq108719 eq28809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108719
  have eq108740 : (σ y) = (M.op x (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq108728 eq108732
    | exact resolve eq108732 eq108728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108732
  have eq108743 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29567 eq108740
    | exact resolve eq108740 eq29567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108740
  have eq108746 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq108743
    | exact resolve eq108743 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108743
  have eq108767 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq108746 eq27
    | exact resolve eq27 eq108746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108746
  have eq108856 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq108767
       have r₂ := eq108728
       grind)
    | exact resolve eq108767 eq108728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108728 eq108767
  have eq110565 : ∀ X0 : G, (M.op (M.op X0 (σ x)) y) = (M.op (M.op X0 (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq45043 eq29754
    | exact resolve eq29754 eq45043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45043
  have eq110592 : ∀ X0 : G, (M.op (M.op X0 (σ x)) y) = (M.op (M.op X0 (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq110565 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110565
  have eq116986 : ∀ X0 : G, (M.op (M.op (σ x) (M.op x y)) (σ x)) ≠ X0 ∨ (M.op (M.op X0 y) (M.op X0 y)) = (M.op (M.op (σ x) (M.op x y)) (σ x)) ∨ (M.op (M.op (σ x) (M.op x y)) (σ x)) = (k (M.op X0 y) (M.op (M.op (σ x) (M.op x y)) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq110592 eq821
    | (have r₁ := eq821 (M.op (M.op (σ x) (M.op x y)) (σ x)) (σ x) y
       have r₂ := eq110592 (σ x)
       grind)
    | (have r₁ := eq821 (M.op (M.op (M.op x y) (σ x)) y) (M.op x y) (σ x)
       have r₂ := eq110592 (M.op x y)
       grind)
    | exact resolve eq821 eq110592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821 eq110592
  have eq117108 : ∀ X0 : G, (M.op (M.op (σ x) (M.op x y)) (σ x)) ≠ X0 ∨ x = (M.op (M.op (σ x) (M.op x y)) (σ x)) ∨ (M.op (M.op (σ x) (M.op x y)) (σ x)) = (k (M.op X0 y) (M.op (M.op (σ x) (M.op x y)) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq28809 eq116986
    | (have j0 := eq116986 X0
       grind)
    | exact resolve eq116986 eq28809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116986
  have eq117170 : ∀ X0 : G, (M.op (M.op (σ x) (M.op x y)) (σ x)) ≠ X0 ∨ (σ x) = (M.op (M.op (σ x) (M.op x y)) (σ x)) ∨ (M.op (M.op (σ x) (M.op x y)) (σ x)) = (k (M.op X0 y) (M.op (M.op (σ x) (M.op x y)) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29567 eq117108
    | (have j0 := eq117108 X0
       grind)
    | exact resolve eq117108 eq29567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117108
  have eq117217 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (σ x) = (M.op (M.op (σ x) (M.op x y)) (σ x)) ∨ (M.op (M.op (σ x) (M.op x y)) (σ x)) = (k (M.op X0 y) (M.op (M.op (σ x) (M.op x y)) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29754 eq117170
    | (have j0 := eq117170 X0
       grind)
    | (have r₁ := eq117170 (M.op x y)
       have r₂ := eq29754 (M.op x y)
       grind)
    | (have r₁ := eq117170 (M.op (M.op (σ x) (M.op (M.op (σ x) (M.op x y)) (σ x))) (σ x))
       have r₂ := eq29754 (M.op (M.op (σ x) (M.op x y)) (σ x))
       grind)
    | exact resolve eq117170 eq29754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117170
  have eq117236 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (M.op x y) = (σ x) ∨ (M.op (M.op (σ x) (M.op x y)) (σ x)) = (k (M.op X0 y) (M.op (M.op (σ x) (M.op x y)) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29754 eq117217
    | (have j0 := eq117217 X0
       grind)
    | (have r₁ := eq117217 (M.op (M.op (σ x) (M.op x y)) (σ x))
       have r₂ := eq29754 (M.op x y)
       grind)
    | (have r₁ := eq117217 x
       have r₂ := eq29754 x
       grind)
    | exact resolve eq117217 eq29754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117217
  have eq117244 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (M.op (M.op (σ x) (M.op x y)) (σ x)) = (k (M.op X0 y) (M.op (M.op (σ x) (M.op x y)) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq117236 X0
       grind)
    | (have r₁ := eq117236 x
       have r₂ := eq60322
       grind)
    | (have r₁ := eq117236 X0
       have r₂ := eq60322
       grind)
    | exact resolve eq117236 eq60322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117236
  have eq117249 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (M.op x y) = (k (M.op X0 y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29754 eq117244
    | (have j0 := eq117244 X0
       grind)
    | (have r₁ := eq117244 (M.op (M.op (σ x) (M.op x y)) (σ x))
       have r₂ := eq29754 (M.op x y)
       grind)
    | (have r₁ := eq117244 x
       have r₂ := eq29754 x
       grind)
    | exact resolve eq117244 eq29754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29754 eq117244
  have eq117251 : (M.op x y) = (k (M.op (M.op x y) y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq117249 (M.op x y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117249
  have eq117255 : (σ (M.op x y)) = (k (σ (M.op (M.op x y) y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq117251 eq41
    | exact resolve eq41 eq117251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq117251
  have eq117261 : (σ (M.op x y)) = (k (σ (M.op (M.op x y) y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq117255
    | exact resolve eq117255 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117255
  have eq117276 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op (M.op x y) y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq117261 eq867
    | (have j0 := eq867 (σ (M.op x y)) (σ (M.op (M.op x y) y))
       grind)
    | (have r₁ := eq867 (σ (M.op x y)) (σ (M.op (M.op x y) y))
       have r₂ := eq117261
       grind)
    | exact resolve eq867 eq117261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867 eq117261
  have eq117277 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op (M.op x y) y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq117276
  have eq117278 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op (M.op x y) y))) ∨ x = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28809 eq117277
    | exact resolve eq117277 eq28809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117277
  have eq117286 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op (M.op x y) y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29567 eq117278
    | exact resolve eq117278 eq29567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117278
  have eq117290 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq108856 eq117286
    | exact resolve eq117286 eq108856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117286
  have eq117294 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28809 eq117290
    | exact resolve eq117290 eq28809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117290
  have eq117296 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq117294
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq117294
    | exact resolve eq117294 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117294
  have eq117308 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq117296 eq29748
    | exact resolve eq29748 eq117296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29748 eq117296
  have eq117355 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq117308
  have eq132483 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X2) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq703 X1 x X2 x
       have i₂ := eq4442 X1 x X2 x X0
       grind)
    | exact superpose eq4442 eq703
    | exact resolve eq703 eq4442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703 eq4442
  have eq154805 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X1 (σ y))) X1) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (M.op x y) = (k y (σ x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq4514 eq65919
    | exact resolve eq65919 eq4514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65919
  have eq156345 : ∀ X1 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (σ x) (M.op X1 (σ y))) X1) ∨ (M.op x y) = (k y (σ x)) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq65929 eq154805
    | exact resolve eq154805 eq65929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154805
  have eq156788 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op X1 (σ y))) X1) ∨ (M.op x y) = (k y (σ x)) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq66335 eq156345
    | exact resolve eq156345 eq66335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66335 eq156345
  have eq179790 : (k (σ x) (σ (M.op x y))) = (k (τ x) (σ (M.op x y))) ∨ (M.op x y) = (k y (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq66117 (M.op (τ x) x)
       have i₂ := eq29054 x (τ x)
       grind)
    | exact superpose eq29054 eq66117
    | exact resolve eq66117 eq29054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29054 eq66117
  have eq179835 : (k (σ x) (σ (M.op x y))) = (k (τ x) (σ (M.op x y))) ∨ (M.op x y) = (k y (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq179790
  have eq179869 : (k (σ x) (σ (M.op x y))) = (k (τ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28824 eq179835
    | exact resolve eq179835 eq28824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179835
  have eq179929 : (σ y) = (k (τ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36116 eq179869
    | exact resolve eq179869 eq36116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36116 eq179869
  have eq179969 : (σ y) = (k (τ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq108856 eq179929
    | exact resolve eq179929 eq108856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108856 eq179929
  have eq179995 : (σ y) = (k x (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29284 eq179969
    | exact resolve eq179969 eq29284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29284 eq179969
  have eq180010 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29567 eq179995
    | exact resolve eq179995 eq29567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179995
  have eq180017 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq28817 eq180010
    | exact resolve eq180010 eq28817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28817 eq180010
  have eq180045 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k y (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq180017 eq75985
    | exact resolve eq75985 eq180017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75985
  have eq180048 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k y (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq180045
  have eq180051 : (σ x) = (σ y) ∨ (M.op x y) = (k y (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq65929 eq180048
    | exact resolve eq180048 eq65929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180048
  have eq180052 : (M.op x y) = (k y (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq180051
  have eq200671 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op x y)) (M.op (σ x) (M.op (σ y) y))) ∨ (M.op x y) = (k y (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39439 eq156788
    | exact resolve eq156788 eq39439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39439 eq156788
  have eq201005 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op x y)) (M.op (σ x) (M.op (σ y) y))) ∨ (M.op x y) = (k y (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq200671
  have eq201143 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op x y)) (M.op (σ x) (M.op (σ y) y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28824 eq201005
    | exact resolve eq201005 eq28824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28824 eq201005
  have eq201262 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op x y)) (M.op (σ x) (M.op (σ x) y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq180017 eq201143
    | exact resolve eq201143 eq180017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180017 eq201143
  have eq201345 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op x y)) (M.op (σ x) (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31587 eq201262
    | exact resolve eq201262 eq31587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31587 eq201262
  have eq201393 : x = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28809 eq201345
    | exact resolve eq201345 eq28809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28809 eq201345
  have eq201416 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29567 eq201393
    | exact resolve eq201393 eq29567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29567 eq201393
  have eq201417 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq201416
  have eq201434 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq201417 eq27
    | exact resolve eq27 eq201417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201437 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq201417 eq825
    | (have r₁ := eq825
       have r₂ := eq201417
       grind)
    | exact resolve eq825 eq201417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201417
  have eq201452 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq201437
  have eq202449 : ∀ X0 : G, (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (k X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq201452 eq66746
    | (have j0 := eq66746 X0
       grind)
    | exact resolve eq66746 eq201452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66746 eq201452
  have eq202471 : ∀ X0 : G, (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (k X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq202449 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202449
  have eq202494 : ∀ X0 : G, x = (M.op x y) ∨ (k X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq202471 X0
       grind)
    | (have r₁ := eq202471 X0
       have r₂ := eq201434
       grind)
    | exact resolve eq202471 eq201434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201434 eq202471
  have eq202507 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq202494 X0
       have j1 := eq730 X0 X0 (σ x)
       grind)
    | (have r₁ := eq202494 (M.op X0 X0)
       have r₂ := eq730 X0 x (k (M.op X0 X0) (σ x))
       grind)
    | (have r₁ := eq202494 X0
       have r₂ := eq730 (σ y) x (σ x)
       grind)
    | exact resolve eq202494 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730 eq202494
  have eq202650 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq202507 eq180052
    | exact resolve eq180052 eq202507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180052
  have eq202655 : ∀ X0 : G, y = (M.op x y) ∨ (M.op X0 X0) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq202507 eq65929
    | (have j0 := eq65929 X0
       grind)
    | exact resolve eq65929 eq202507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65929 eq202507
  have eq202710 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq202655 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202655
  have eq202715 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq202650
  have eq202987 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq202715 eq31
    | exact resolve eq31 eq202715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202715
  have eq203250 : x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq202987
    | exact resolve eq202987 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202987
  have eq203285 : y = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq60236 eq203250
    | exact resolve eq203250 eq60236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203250
  have eq203421 : (M.op x y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq60252
       have i₂ := eq203285
       grind)
    | exact superpose eq203285 eq60252
    | exact resolve eq60252 eq203285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60252 eq203285
  have eq203557 : (M.op x y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq203421
  have eq216911 : (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq203557 eq202710
    | exact resolve eq202710 eq203557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202710 eq203557
  have eq216955 : (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq216911
  have eq217119 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq216955
       have r₂ := eq60322
       grind)
    | exact resolve eq216955 eq60322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216955
  have eq217398 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq217119
       grind)
    | exact superpose eq217119 eq24
    | exact resolve eq24 eq217119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217719 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq217398
    | exact resolve eq217398 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217398
  have eq217794 : (σ y) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq217719 eq66808
    | (have r₁ := eq66808
       have r₂ := eq217719
       grind)
    | exact resolve eq66808 eq217719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66808
  have eq217805 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq217719 eq117355
    | exact resolve eq117355 eq217719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117355
  have eq217824 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq217805
  have eq217836 : (σ y) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ y) = (k (σ y) (σ x)) := by grind
  clear eq217794
  have eq217837 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq217836
  have eq217852 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq217824
    | exact resolve eq217824 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217824
  have eq221571 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq217852 eq27
    | exact resolve eq27 eq217852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217852
  have eq221741 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq221571
       have r₂ := eq217719
       grind)
    | exact resolve eq221571 eq217719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217719 eq221571
  have eq221773 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq221741 eq825
    | (have r₁ := eq825
       have r₂ := eq221741
       grind)
    | exact resolve eq825 eq221741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq221782 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 (σ y))) X1) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq221741 eq4514
    | exact resolve eq4514 eq221741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4514 eq221741
  have eq221788 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq221773
  have eq221794 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq217837 eq221788
    | exact resolve eq221788 eq217837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217837 eq221788
  have eq221795 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq221794
  have eq222165 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 (σ y))) X1) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq221795 eq4507
    | exact resolve eq4507 eq221795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4507 eq221795
  have eq222310 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq221782 eq222165
    | exact resolve eq222165 eq221782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221782 eq222165
  have eq222311 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq222310
  have eq228769 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq222311 eq31
    | exact resolve eq31 eq222311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq222311
  have eq229069 : x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq228769
    | exact resolve eq228769 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228769
  have eq229121 : y = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq60236 eq229069
    | exact resolve eq229069 eq60236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60236 eq229069
  have eq229168 : (M.op x y) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq217119 eq229121
    | exact resolve eq229121 eq217119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217119 eq229121
  have eq229189 : x = (M.op x y) := by
    first
    | (have r₁ := eq229168
       have r₂ := eq60322
       grind)
    | exact resolve eq229168 eq60322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60322 eq229168
  have eq229198 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq229189
       grind)
    | exact superpose eq229189 eq18
    | exact resolve eq18 eq229189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229199 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq229189
       grind)
    | exact superpose eq229189 eq22
    | exact resolve eq22 eq229189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq229203 : ∀ X0 X1 : G, (M.op (M.op X0 X0) y) = (M.op (M.op (M.op X1 X1) (M.op x y)) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq195 X1 X0
       have i₂ := eq229189
       grind)
    | exact superpose eq229189 eq195
    | exact resolve eq195 eq229189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq229208 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (k y (M.op x y)) := by
    first
    | (have i₁ := eq824
       have i₂ := eq229189
       grind)
    | exact superpose eq229189 eq824
    | (have r₁ := eq824
       have r₂ := eq229189
       grind)
    | exact resolve eq824 eq229189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq229222 : (M.op x y) = (k y (M.op x y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq229208
  have eq229225 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq229199 eq20
    | exact resolve eq20 eq229199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229421 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq229198 eq16
    | exact resolve eq16 eq229198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229426 : ∀ X0 : G, (M.op x y) = (M.op (M.op (τ (M.op X0 X0)) y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq229198 eq2706
    | exact resolve eq2706 eq229198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2706 eq229198
  have eq233110 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq229222 eq36
    | exact resolve eq36 eq229222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq229222
  have eq233125 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq233110
    | exact resolve eq233110 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233110
  have eq233129 : (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq229225 eq233125
    | exact resolve eq233125 eq229225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233125
  have eq233595 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq233129 eq833
    | exact resolve eq833 eq233129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833 eq233129
  have eq233616 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq233595
  have eq247257 : ∀ X0 X2 : G, y = (M.op (M.op (M.op (M.op X0 X0) (M.op x y)) (M.op x y)) (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq736 X2 x y
       have i₂ := eq229203 x X0
       grind)
    | exact superpose eq229203 eq736
    | exact resolve eq736 eq229203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq260253 : (M.op x y) = (M.op (M.op (τ (σ x)) y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq233616 eq229426
    | exact resolve eq229426 eq233616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229426 eq233616
  have eq260365 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq29 eq260253
    | exact resolve eq260253 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq260253
  have eq260588 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq260365
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq260365
    | exact resolve eq260365 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq260365
  have eq260749 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq2302 x (M.op x y)
       grind)
    | (have r₁ := eq260588
       have r₂ := eq2302 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq260588
       have r₂ := eq2302 y (M.op x y)
       grind)
    | exact resolve eq260588 eq2302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2302 eq260588
  have eq261478 : ∀ X0 : G, y = (M.op (M.op (M.op (M.op X0 X0) (M.op x y)) (M.op x y)) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq260749 eq247257
    | exact resolve eq247257 eq260749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247257 eq260749
  have eq261555 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq261478 x
       have i₂ := eq132483 x sF0 sF0
       grind)
    | exact superpose eq132483 eq261478
    | exact resolve eq261478 eq132483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132483 eq261478
  have eq261982 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq261555 eq27
    | exact resolve eq27 eq261555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261555
  have eq262005 : y = (M.op x y) := by
    first
    | (have r₁ := eq261982
       have r₂ := eq229225
       grind)
    | exact resolve eq261982 eq229225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261982
  have eq262008 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq262005
       grind)
    | exact superpose eq262005 eq24
    | exact resolve eq24 eq262005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq262034 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op x y)) = (M.op (M.op (M.op X1 X1) x) (M.op (M.op X2 X2) (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4464 X0 X1 X2
       have i₂ := eq262005
       grind)
    | exact superpose eq262005 eq4464
    | exact resolve eq4464 eq262005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4464
  have eq262161 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op x y)) = (M.op (M.op (M.op X1 X1) (M.op x y)) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq229203 X0 X1
       have i₂ := eq262005
       grind)
    | exact superpose eq262005 eq229203
    | exact resolve eq229203 eq262005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229203
  have eq262167 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op X0 X0) (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq229421 X0
       have i₂ := eq262005
       grind)
    | exact superpose eq262005 eq229421
    | exact resolve eq229421 eq262005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229421 eq262005
  have eq262189 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq262167 eq262161
    | exact resolve eq262161 eq262167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262161 eq262167
  have eq262195 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op x y)) = (M.op (M.op (M.op X1 X1) (M.op x y)) (M.op (M.op X2 X2) (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq262034 X0 X1 X2
       have i₂ := eq229189
       grind)
    | exact superpose eq229189 eq262034
    | exact resolve eq262034 eq229189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229189 eq262034
  have eq262209 : (σ x) = (σ y) := by
    first
    | exact superpose eq229199 eq262008
    | exact resolve eq262008 eq229199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229199 eq262008
  have eq262215 : ∀ X0 X2 : G, (M.op X2 X2) = (M.op (M.op X0 X0) (M.op x y)) := by
    intro X0 X2
    first
    | (have i₁ := eq262195 X0 x X2
       have i₂ := eq16 (M.op X2 X2) x sF0
       grind)
    | exact superpose eq16 eq262195
    | exact resolve eq262195 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262195
  have eq262218 : ∀ X2 : G, (M.op x y) = (M.op X2 X2) := by
    intro X2
    first
    | exact superpose eq262189 eq262215
    | exact resolve eq262215 eq262189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262215
  have eq262219 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq262209 eq26
    | exact resolve eq26 eq262209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq262248 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op X0 X0)) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq262209 eq2525
    | exact resolve eq2525 eq262209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2525 eq262209
  have eq262370 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq262248 x
       have i₂ := eq262218 x
       grind)
    | exact superpose eq262218 eq262248
    | exact resolve eq262248 eq262218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262248
  have eq262390 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq262219
       have i₂ := eq262218 sF2
       grind)
    | exact superpose eq262218 eq262219
    | exact resolve eq262219 eq262218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262218 eq262219
  have eq262395 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20 eq262370
    | exact resolve eq262370 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq262370
  have eq262409 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ x)) (M.op x y)) := by
    first
    | exact superpose eq262390 eq262395
    | exact resolve eq262395 eq262390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262395
  have eq262417 : (σ x) = (M.op (M.op (σ x) (σ x)) (M.op x y)) := by
    first
    | exact superpose eq229225 eq262409
    | exact resolve eq262409 eq229225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262409
  have eq262422 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq262189 eq262417
    | exact resolve eq262417 eq262189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262189 eq262417
  have eq262433 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq262390 eq27
    | exact resolve eq27 eq262390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq262390
  have eq262536 : (M.op x y) ≠ (σ x) := by
    first
    | exact superpose eq229225 eq262433
    | exact resolve eq262433 eq229225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229225 eq262433
  have eq262550 : False := by grind
  exact eq262550

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then Y else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_y_y_pyx_Equation2146 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (k X0 (M.op X0 X0))
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
  have eq86 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq42 eq15
    | exact resolve eq15 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
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
  have eq175 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : x ≠ (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq365 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq538 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq16 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq539 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
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
  have eq546 : ∀ X0 X1 : G, (M.op (M.op X1 X1) y) = (M.op (M.op (M.op X0 X0) (M.op x y)) x) := by
    intro X0 X1
    first
    | exact superpose eq539 eq16
    | exact resolve eq16 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq554 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq538 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq538 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq538 eq538
    | exact resolve eq538 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq577 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X2 ∨ (k X1 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq554 X0 X1
       grind)
    | (have i₁ := eq13 X1 X2
       have i₂ := eq554 X1 X0
       grind)
    | exact superpose eq554 eq13
    | (have j0 := eq13 X0 X2
       grind)
    | (have r₁ := eq13 X1 (M.op X0 X0)
       have r₂ := eq554 X0 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq554 X0 X1
       grind)
    | exact resolve eq13 eq554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq579 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq175 X1
       have i₂ := eq554 X0 X1
       grind)
    | (have i₁ := eq175 X0
       have i₂ := eq554 X0 X1
       grind)
    | exact superpose eq554 eq175
    | exact resolve eq175 eq554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq583 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq554 X0 X2
       grind)
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq554 X2 X0
       grind)
    | exact superpose eq554 eq16
    | exact resolve eq16 eq554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq588 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X2 (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 (M.op X1 X1)
       have i₂ := eq554 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq16 X2 X1 (M.op X1 X1)
       have i₂ := eq554 (M.op X1 X1) X0
       grind)
    | exact superpose eq554 eq16
    | exact resolve eq16 eq554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq592 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq365 X1 (M.op X0 X0)
       have i₂ := eq579 X0 (σ X1)
       grind)
    | exact superpose eq579 eq365
    | exact resolve eq365 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq593 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (M.op X0 X0)
       have i₂ := eq579 X0 (τ X1)
       grind)
    | exact superpose eq579 eq35
    | exact resolve eq35 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq599 : ∀ X0 : G, (τ (M.op X0 X0)) = (k y (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq108 (M.op X0 X0)
       have i₂ := eq579 X0 sF3
       grind)
    | exact superpose eq579 eq108
    | exact resolve eq108 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq718 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X0) = (M.op (M.op X2 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq538 (M.op X1 X1) X1 (M.op (M.op X2 X2) X0)
       have i₂ := eq583 (M.op X1 X1) X2 X0
       grind)
    | exact superpose eq583 eq538
    | exact resolve eq538 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq834 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X1
       have i₂ := eq554 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq554 X0 X1
       grind)
    | exact superpose eq554 eq11
    | (have j0 := eq11 X0 (k X1 X1)
       grind)
    | exact resolve eq11 eq554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq840 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq841 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq860 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X2) X0) (k X0 X1)) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq905 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq834 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834
  have eq1469 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq554 X2 X1
       have i₂ := eq905 X2 X0
       grind)
    | exact superpose eq905 eq554
    | (have j1 := eq905 X1 X0
       grind)
    | exact resolve eq554 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1520 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq593 X1 (σ (M.op X1 X1))
       have i₂ := eq905 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq905 eq593
    | (have j1 := eq905 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq593 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq1522 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq592 X1 (τ (M.op X1 X1))
       have i₂ := eq905 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq905 eq592
    | (have j1 := eq905 X0 (τ (M.op X1 X1))
       grind)
    | exact resolve eq592 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592 eq905
  have eq1528 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1522 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1522
  have eq1529 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1520 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1520
  have eq1575 : ∀ X0 X2 X3 : G, (M.op (M.op (τ (M.op X0 X0)) X2) (M.op X3 X2)) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq16 X3 x X2
       have i₂ := eq1528 x X0
       grind)
    | exact superpose eq1528 eq16
    | exact resolve eq16 eq1528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1608 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (τ (M.op X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq1528 X2 X0
       grind)
    | exact superpose eq1528 eq16
    | exact resolve eq16 eq1528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1614 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq538 X1 X2 (M.op X1 (M.op X2 X2))
       have i₂ := eq1528 (M.op X1 (M.op X2 X2)) X0
       grind)
    | exact superpose eq1528 eq538
    | exact resolve eq538 eq1528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1654 : ∀ X0 X2 : G, (σ (M.op X0 X0)) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq1529 x X2
       have i₂ := eq1529 x X0
       grind)
    | exact superpose eq1529 eq1529
    | exact resolve eq1529 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1670 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1529 X1 x
       have i₂ := eq1529 x X0
       grind)
    | exact superpose eq1529 eq1529
    | exact resolve eq1529 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1680 : ∀ X0 X2 X3 : G, (M.op (M.op (σ (M.op X0 X0)) X2) (M.op X3 X2)) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq16 X3 x X2
       have i₂ := eq1529 x X0
       grind)
    | exact superpose eq1529 eq16
    | exact resolve eq16 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1690 : ∀ X0 X2 X3 : G, (σ (M.op X0 X0)) ≠ X2 ∨ (k X3 X2) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq577 x X3 X2
       have i₂ := eq1529 x X0
       grind)
    | exact superpose eq1529 eq577
    | (have j0 := eq577 X0 X3 X2
       grind)
    | (have r₁ := eq577 X0 x (σ (M.op x x))
       have r₂ := eq1529 X0 x
       grind)
    | exact resolve eq577 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577
  have eq1708 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq718 X2 X1 x
       have i₂ := eq1529 x X0
       grind)
    | exact superpose eq1529 eq718
    | exact resolve eq718 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1713 : ∀ X0 X2 : G, (σ (M.op X0 X0)) = (τ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq1528 x X2
       have i₂ := eq1529 x X0
       grind)
    | exact superpose eq1529 eq1528
    | exact resolve eq1528 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1717 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq588 X1 X2 (M.op X2 X2)
       have i₂ := eq1529 (M.op X2 X2) X0
       grind)
    | exact superpose eq1529 eq588
    | exact resolve eq588 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq1721 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq538 X1 X2 (M.op X1 (M.op X2 X2))
       have i₂ := eq1529 (M.op X1 (M.op X2 X2)) X0
       grind)
    | exact superpose eq1529 eq538
    | exact resolve eq538 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq1998 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1654 X1 x
       have i₂ := eq1529 x X0
       grind)
    | exact superpose eq1529 eq1654
    | exact resolve eq1654 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2170 : ∀ X0 X2 : G, (τ (M.op X2 X2)) = (σ (σ (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq1528 x X2
       have i₂ := eq1670 X0 x
       grind)
    | exact superpose eq1670 eq1528
    | exact resolve eq1528 eq1670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2171 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1529 X1 x
       have i₂ := eq1670 X0 x
       grind)
    | exact superpose eq1670 eq1529
    | exact resolve eq1529 eq1670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2178 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (σ (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1654 X1 x
       have i₂ := eq1670 X0 x
       grind)
    | exact superpose eq1670 eq1654
    | exact resolve eq1654 eq1670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1654 eq1670
  have eq2575 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq840
       grind)
    | exact superpose eq840 eq40
    | exact resolve eq40 eq840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq2576 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2575
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2575
    | exact resolve eq2575 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2575
  have eq2578 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq2576
    | exact resolve eq2576 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2576
  have eq2924 : ∀ X0 X1 : G, (τ (k (σ (M.op X0 X0)) (σ (M.op x y)))) = (k (σ (M.op X1 X1)) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 (σ (M.op X1 X1))
       have i₂ := eq1998 X1 X0
       grind)
    | exact superpose eq1998 eq86
    | exact resolve eq86 eq1998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1998
  have eq2931 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op x y)) = (k (σ (M.op X1 X1)) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq86 eq2924
    | exact resolve eq2924 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq2924
  have eq22716 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2578 eq841
    | exact resolve eq841 eq2578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2578
  have eq22727 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq22716
       have r₂ := eq27
       grind)
    | exact resolve eq22716 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22716
  have eq22771 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq22727 eq599
    | exact resolve eq599 eq22727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599 eq22727
  have eq23038 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq22771
    | exact resolve eq22771 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22771
  have eq23126 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq23038
       have r₂ := eq176
       grind)
    | exact resolve eq23038 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq23038
  have eq23176 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq23126
       have r₂ := eq13 y x
       grind)
    | exact resolve eq23126 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23126
  have eq23285 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq23176
       grind)
    | exact superpose eq23176 eq37
    | exact resolve eq37 eq23176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq23176
  have eq23295 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23285
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23285
    | exact resolve eq23285 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23285
  have eq23297 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq23295
       have r₂ := eq177
       grind)
    | exact resolve eq23295 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq23295
  have eq23302 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq23297 eq841
    | exact resolve eq841 eq23297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841
  have eq23304 : (τ (σ x)) = (k y (τ (σ x))) := by
    first
    | exact superpose eq23297 eq108
    | exact resolve eq108 eq23297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq23297
  have eq23309 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23302
  have eq23314 : x = (k y x) := by
    first
    | exact superpose eq30 eq23304
    | exact resolve eq23304 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23304
  have eq23318 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq840
       have i₂ := eq23314
       grind)
    | exact superpose eq23314 eq840
    | exact resolve eq840 eq23314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840 eq23314
  have eq23324 : x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq23318
  have eq23351 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq23309 eq554
    | exact resolve eq554 eq23309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23357 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (σ x)) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq23309 eq583
    | exact resolve eq583 eq23309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq23372 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (σ x) X1) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq23309 eq718
    | exact resolve eq718 eq23309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23378 : ∀ X0 : G, (M.op X0 X0) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq23309 eq1528
    | exact resolve eq1528 eq23309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23379 : ∀ X0 : G, (M.op X0 X0) = (σ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq23309 eq1529
    | exact resolve eq1529 eq23309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23395 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (τ (σ x))) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq23309 eq1608
    | exact resolve eq1608 eq23309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1608
  have eq23401 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq23309 eq1614
    | exact resolve eq1614 eq23309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1614
  have eq23467 : ∀ X0 : G, (M.op X0 X0) = (σ (σ (σ (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq23309 eq2171
    | exact resolve eq2171 eq23309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2171 eq23309
  have eq23570 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq30 eq23401
    | exact resolve eq23401 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23401
  have eq23576 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) x) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq30 eq23395
    | exact resolve eq23395 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23395
  have eq23592 : ∀ X0 : G, (M.op X0 X0) = x ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq30 eq23378
    | exact resolve eq23378 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23378
  have eq23594 : ∀ X1 : G, (M.op (σ x) X1) = (M.op (σ (σ x)) X1) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq23379 eq23372
    | exact resolve eq23372 eq23379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23372
  have eq23604 : ∀ X1 : G, (M.op (M.op (σ (σ x)) X1) (σ x)) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq23379 eq23357
    | exact resolve eq23357 eq23379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23357 eq23379
  have eq23645 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq23351 eq23570
    | exact resolve eq23570 eq23351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23570
  have eq23650 : ∀ X1 : G, (M.op (M.op (σ x) X1) x) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq23351 eq23576
    | exact resolve eq23576 eq23351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23576
  have eq23661 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | exact superpose eq23351 eq23592
    | exact resolve eq23592 eq23351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23592
  have eq23662 : ∀ X1 : G, (M.op (M.op (σ x) X1) (σ x)) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq23594 eq23604
    | exact resolve eq23604 eq23594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23594 eq23604
  have eq23731 : (σ (M.op x y)) ≠ (σ x) ∨ x = (σ x) := by
    first
    | exact superpose eq23661 eq27
    | exact resolve eq27 eq23661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23810 : ∀ X0 : G, (M.op X0 X0) = x ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq554 y X0
       have i₂ := eq23324
       grind)
    | exact superpose eq23324 eq554
    | exact resolve eq554 eq23324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq23831 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op x X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq718 X1 X0 y
       have i₂ := eq23324
       grind)
    | exact superpose eq23324 eq718
    | exact resolve eq718 eq23324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq23836 : ∀ X0 X1 : G, x = (k X0 X0) ∨ (M.op X1 X1) = X0 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1469 X0 y X1
       have i₂ := eq23324
       grind)
    | exact superpose eq23324 eq1469
    | (have j0 := eq1469 X0 X1 X1
       grind)
    | exact resolve eq1469 eq23324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23837 : ∀ X0 : G, (M.op X0 X0) = (τ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1528 X0 y
       have i₂ := eq23324
       grind)
    | exact superpose eq23324 eq1528
    | exact resolve eq1528 eq23324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1528
  have eq23838 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1529 X0 y
       have i₂ := eq23324
       grind)
    | exact superpose eq23324 eq1529
    | exact resolve eq1529 eq23324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1529
  have eq23876 : ∀ X0 X1 : G, (σ x) ≠ X0 ∨ (k X1 X0) = X0 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1690 y X0 X1
       have i₂ := eq23324
       grind)
    | exact superpose eq23324 eq1690
    | (have j0 := eq1690 X0 X0 X1
       grind)
    | exact resolve eq1690 eq23324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1690
  have eq23879 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (σ x) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1708 y X0 X1
       have i₂ := eq23324
       grind)
    | exact superpose eq23324 eq1708
    | exact resolve eq1708 eq23324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1708
  have eq23881 : ∀ X0 : G, (σ x) = (τ (M.op X0 X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1713 y X0
       have i₂ := eq23324
       grind)
    | exact superpose eq23324 eq1713
    | exact resolve eq1713 eq23324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1713
  have eq23889 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1721 y X0 X1
       have i₂ := eq23324
       grind)
    | exact superpose eq23324 eq1721
    | exact resolve eq1721 eq23324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1721
  have eq23925 : ∀ X0 : G, (τ (M.op X0 X0)) = (σ (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2170 y X0
       have i₂ := eq23324
       grind)
    | exact superpose eq23324 eq2170
    | exact resolve eq2170 eq23324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2170
  have eq23928 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (σ (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2178 y X0
       have i₂ := eq23324
       grind)
    | exact superpose eq23324 eq2178
    | exact resolve eq2178 eq23324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2178
  have eq23944 : ∀ X0 : G, (k (M.op X0 X0) (M.op x y)) = (k (σ x) (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2931 X0 y
       have i₂ := eq23324
       grind)
    | exact superpose eq23324 eq2931
    | exact resolve eq2931 eq23324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2931
  have eq23973 : ∀ X0 : G, y = (M.op (M.op (τ (M.op X0 X0)) y) x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1575 X0 y y
       have i₂ := eq23324
       grind)
    | exact superpose eq23324 eq1575
    | exact resolve eq1575 eq23324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1575 eq23324
  have eq23989 : ∀ X0 : G, (k (M.op X0 X0) (M.op x y)) = (k (σ x) (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq23944 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23944
    | (have j0 := eq23944 X0
       grind)
    | exact resolve eq23944 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23944
  have eq23999 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (σ (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq23928 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23928
    | (have j0 := eq23928 X0
       grind)
    | exact resolve eq23928 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23928
  have eq24002 : ∀ X0 : G, (τ (M.op X0 X0)) = (σ (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq23925 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23925
    | (have j0 := eq23925 X0
       grind)
    | exact resolve eq23925 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23925
  have eq24024 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq23889 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23889
    | (have j0 := eq23889 X0 X1
       grind)
    | exact resolve eq23889 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23889
  have eq24032 : ∀ X0 : G, (σ x) = (τ (M.op X0 X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq23881 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23881
    | (have j0 := eq23881 X0
       grind)
    | exact resolve eq23881 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23881
  have eq24034 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (σ x) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq23879 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23879
    | (have j0 := eq23879 X0 X1
       grind)
    | exact resolve eq23879 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23879
  have eq24037 : ∀ X0 X1 : G, (σ x) ≠ X0 ∨ (k X1 X0) = X0 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq23876 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23876
    | (have j0 := eq23876 X0 X1
       grind)
    | (have r₁ := eq23876 (σ x) X1
       have r₂ := eq22
       grind)
    | exact resolve eq23876 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23876
  have eq24067 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq23838 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23838
    | (have j0 := eq23838 X0
       grind)
    | exact resolve eq23838 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23838
  have eq24069 : ∀ X1 : G, (M.op x X1) = (M.op (τ x) X1) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq23837 eq23831
    | exact resolve eq23831 eq23837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23831 eq23837
  have eq24095 : (k x (M.op x y)) = (k (σ x) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23810 eq23989
    | exact resolve eq23989 eq23810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23989
  have eq24100 : (σ x) = (σ (σ (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23810 eq23999
    | exact resolve eq23999 eq23810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23999
  have eq24103 : (τ x) = (σ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23810 eq24002
    | exact resolve eq24002 eq23810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24002
  have eq24117 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq23810 eq24024
    | exact resolve eq24024 eq23810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24024
  have eq24124 : (σ x) = (τ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23810 eq24032
    | exact resolve eq24032 eq23810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24032
  have eq24125 : ∀ X1 : G, (M.op (σ x) X1) = (M.op x X1) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq23810 eq24034
    | exact resolve eq24034 eq23810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24034
  have eq24154 : (σ x) = (σ (σ (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24100
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24100
    | exact resolve eq24100 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24100
  have eq24187 : (σ x) = (σ (τ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24103 eq24154
    | exact resolve eq24154 eq24103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24103 eq24154
  have eq24207 : x = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24187
       have i₂ := eq14 x
       grind)
    | exact superpose eq14 eq24187
    | exact resolve eq24187 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24187
  have eq24228 : (M.op x y) = (M.op (σ x) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq24207
       grind)
    | exact superpose eq24207 eq18
    | exact resolve eq18 eq24207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24230 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k (σ x) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq24207
       grind)
    | exact superpose eq24207 eq36
    | exact resolve eq36 eq24207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq24247 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) := by grind
  have eq27075 : ∀ X0 X1 : G, (M.op (σ x) (M.op X1 (σ (M.op X0 X0)))) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1680 X0 (σ (M.op X0 X0)) X1
       have i₂ := eq24067 (σ (M.op X0 X0))
       grind)
    | exact superpose eq24067 eq1680
    | exact resolve eq1680 eq24067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1680 eq24067
  have eq27103 : ∀ X1 : G, (M.op (σ x) (M.op X1 (σ x))) = X1 ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq23810 eq27075
    | exact resolve eq27075 eq23810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27075
  have eq27398 : ∀ X1 : G, (M.op (σ x) (M.op X1 (σ x))) = X1 ∨ x = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq27103 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq27103
    | (have j0 := eq27103 X1
       grind)
    | exact resolve eq27103 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27103
  have eq33592 : ∀ X0 X1 : G, (M.op (M.op X1 X1) y) = (M.op (M.op (M.op X0 X0) (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq546 X0 X1
       have i₂ := eq23645 (M.op (M.op X0 X0) sF0)
       grind)
    | exact superpose eq23645 eq546
    | exact resolve eq546 eq23645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546 eq23645
  have eq33653 : ∀ X1 : G, (M.op (M.op X1 X1) y) = (M.op (M.op (σ x) (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq23351 eq33592
    | exact resolve eq33592 eq23351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33592
  have eq33879 : (M.op (σ x) y) = (M.op (M.op (σ x) (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23351 eq33653
    | exact resolve eq33653 eq23351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23351 eq33653
  have eq34040 : (M.op x y) = (M.op (σ x) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23662 eq33879
    | exact resolve eq33879 eq23662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23662 eq33879
  have eq34386 : y = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34040 eq23650
    | exact resolve eq23650 eq34040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23650 eq34040
  have eq34439 : y = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq34386
  have eq34478 : y = (M.op (M.op x y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23661 eq34439
    | exact resolve eq34439 eq23661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23661 eq34439
  have eq118035 : ∀ X0 : G, y = (k x (M.op (τ (M.op X0 X0)) y)) ∨ x = (M.op x y) ∨ (M.op (τ (M.op X0 X0)) y) = (M.op (M.op (τ (M.op X0 X0)) y) x) ∨ (M.op x x) = (M.op (τ (M.op X0 X0)) y) := by
    intro X0
    first
    | (have i₁ := eq23973 X0
       have i₂ := eq11 x (M.op (τ (M.op X0 X0)) y)
       grind)
    | exact superpose eq11 eq23973
    | (have j1 := eq11 x (M.op (τ (M.op X0 X0)) y)
       grind)
    | exact resolve eq23973 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118042 : ∀ X0 : G, y = (k x (M.op (τ (M.op X0 X0)) y)) ∨ y = (M.op (τ (M.op X0 X0)) y) ∨ (M.op x x) = (M.op (τ (M.op X0 X0)) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq11 x (M.op (τ (M.op X0 X0)) y)
       have i₂ := eq23973 X0
       grind)
    | exact superpose eq23973 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq23973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23973
  have eq118096 : ∀ X0 : G, y = (k x (M.op (τ x) y)) ∨ y = (M.op (τ (M.op X0 X0)) y) ∨ (M.op x x) = (M.op (τ (M.op X0 X0)) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq23810 eq118042
    | (have j0 := eq118042 X0
       grind)
    | exact resolve eq118042 eq23810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118042
  have eq118100 : ∀ X0 : G, y = (k x (M.op (τ x) y)) ∨ x = (M.op x y) ∨ (M.op (τ (M.op X0 X0)) y) = (M.op (M.op (τ (M.op X0 X0)) y) x) ∨ (M.op x x) = (M.op (τ (M.op X0 X0)) y) := by
    intro X0
    first
    | exact superpose eq23810 eq118035
    | (have j0 := eq118035 X0
       grind)
    | exact resolve eq118035 eq23810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118035
  have eq118208 : ∀ X0 : G, y = (k x (M.op (τ x) y)) ∨ y = (M.op (τ x) y) ∨ (M.op x x) = (M.op (τ (M.op X0 X0)) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq23810 eq118096
    | (have j0 := eq118096 X0
       grind)
    | exact resolve eq118096 eq23810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118096
  have eq118211 : ∀ X0 : G, y = (k x (M.op (τ x) y)) ∨ x = (M.op x y) ∨ (M.op (τ x) y) = (M.op (M.op (τ x) y) x) ∨ (M.op x x) = (M.op (τ (M.op X0 X0)) y) := by
    intro X0
    first
    | exact superpose eq23810 eq118100
    | (have j0 := eq118100 X0
       grind)
    | exact resolve eq118100 eq23810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118100
  have eq118300 : y = (k x (M.op (τ x) y)) ∨ y = (M.op (τ x) y) ∨ (M.op x x) = (M.op (τ x) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23810 eq118208
    | exact resolve eq118208 eq23810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118208
  have eq118301 : y = (k x (M.op (τ x) y)) ∨ x = (M.op x y) ∨ (M.op (τ x) y) = (M.op (M.op (τ x) y) x) ∨ (M.op x x) = (M.op (τ x) y) := by
    first
    | exact superpose eq23810 eq118211
    | exact resolve eq118211 eq23810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118211
  have eq118381 : y = (k x (M.op (τ x) y)) ∨ y = (M.op (τ x) y) ∨ x = (M.op (τ x) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23810 eq118300
    | exact resolve eq118300 eq23810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118300
  have eq118382 : y = (k x (M.op (τ x) y)) ∨ x = (M.op x y) ∨ (M.op (τ x) y) = (M.op (M.op (τ x) y) x) ∨ x = (M.op (τ x) y) := by
    first
    | exact superpose eq23810 eq118301
    | exact resolve eq118301 eq23810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118301
  have eq118432 : y = (k x (M.op x y)) ∨ y = (M.op (τ x) y) ∨ x = (M.op (τ x) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24069 eq118381
    | exact resolve eq118381 eq24069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118381
  have eq118433 : y = (k x (M.op x y)) ∨ x = (M.op x y) ∨ (M.op (τ x) y) = (M.op (M.op (τ x) y) x) ∨ x = (M.op (τ x) y) := by
    first
    | exact superpose eq24069 eq118382
    | exact resolve eq118382 eq24069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118382
  have eq118470 : y = (k x (M.op x y)) ∨ y = (M.op (τ x) y) ∨ x = (M.op (τ x) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq118432
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq118432
    | exact resolve eq118432 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118432
  have eq118471 : y = (k x (M.op x y)) ∨ x = (M.op x y) ∨ (M.op (τ x) y) = (M.op (M.op (τ x) y) x) ∨ x = (M.op (τ x) y) := by
    first
    | (have i₁ := eq118433
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq118433
    | exact resolve eq118433 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118433
  have eq118495 : y = (k (σ x) (M.op x y)) ∨ y = (M.op (τ x) y) ∨ x = (M.op (τ x) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24095 eq118470
    | exact resolve eq118470 eq24095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118470
  have eq118496 : y = (k x (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op (τ x) y) := by
    first
    | exact superpose eq24069 eq118471
    | exact resolve eq118471 eq24069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24069 eq118471
  have eq118505 : y = (k (σ x) (M.op x y)) ∨ y = (M.op (σ x) y) ∨ x = (M.op (τ x) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24124 eq118495
    | exact resolve eq118495 eq24124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118495
  have eq118506 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op (τ x) y) := by
    first
    | (have i₁ := eq118496
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq118496
    | exact resolve eq118496 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq118496
  have eq118511 : y = (k (σ x) (M.op x y)) ∨ y = (M.op (σ x) y) ∨ x = (M.op (σ x) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24124 eq118505
    | exact resolve eq118505 eq24124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118505
  have eq118512 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (k (σ x) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op (τ x) y) := by
    first
    | exact superpose eq24095 eq118506
    | exact resolve eq118506 eq24095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24095 eq118506
  have eq118515 : y = (k (σ x) (M.op x y)) ∨ y = (M.op (σ x) y) ∨ (σ x) = (M.op (σ x) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24207 eq118511
    | exact resolve eq118511 eq24207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118511
  have eq118516 : (M.op x y) = (M.op (M.op x y) (σ x)) ∨ y = (k (σ x) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op (τ x) y) := by
    first
    | exact superpose eq24117 eq118512
    | exact resolve eq118512 eq24117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24117 eq118512
  have eq118517 : y = (k (σ x) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24228 eq118515
    | exact resolve eq118515 eq24228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118515
  have eq118518 : (M.op x y) = (M.op (M.op x y) (σ x)) ∨ y = (k (σ x) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op (σ x) y) := by
    first
    | exact superpose eq24124 eq118516
    | exact resolve eq118516 eq24124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24124 eq118516
  have eq118519 : y = (k (σ x) (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24228 eq118517
    | exact resolve eq118517 eq24228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118517
  have eq118520 : (M.op x y) = (M.op (M.op x y) (σ x)) ∨ y = (k (σ x) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) y) := by
    first
    | exact superpose eq24207 eq118518
    | exact resolve eq118518 eq24207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118518
  have eq118521 : y = (k (σ x) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq118519
       have r₂ := eq24247
       grind)
    | exact resolve eq118519 eq24247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118519
  have eq118522 : (M.op x y) = (M.op (M.op x y) (σ x)) ∨ y = (k (σ x) (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq24228 eq118520
    | exact resolve eq118520 eq24228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24228 eq118520
  have eq118523 : (M.op x y) = (M.op (M.op x y) (σ x)) ∨ y = (k (σ x) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq118522
       have r₂ := eq24247
       grind)
    | exact resolve eq118522 eq24247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118522
  have eq121935 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (σ x) (M.op x y)) ∨ y = (k (σ x) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq118523 eq28
    | (have j0 := eq28 (σ x) (M.op x y)
       grind)
    | (have r₁ := eq28 (σ x) (M.op x y)
       have r₂ := eq118523
       grind)
    | (have r₁ := eq28 y x
       have r₂ := eq118523
       grind)
    | exact resolve eq28 eq118523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118523
  have eq121950 : (M.op x y) = (k (σ x) (M.op x y)) ∨ y = (k (σ x) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq121935
  have eq122163 : y ≠ (M.op x y) ∨ y = (k (σ x) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq121950
  have eq122168 : y = (k (σ x) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq122163
       have r₂ := eq118521
       grind)
    | exact resolve eq122163 eq118521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118521 eq122163
  have eq122174 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122168 eq24230
    | exact resolve eq24230 eq122168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24230 eq122168
  have eq122180 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq122174
  have eq122187 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq122180
    | exact resolve eq122180 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122180
  have eq122191 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq122187
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq122187
    | exact resolve eq122187 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122187
  have eq122203 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op X0 X0) (σ x)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq122191 eq860
    | (have j0 := eq860 (σ x) (σ (M.op x y)) x
       grind)
    | exact resolve eq860 eq122191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860
  have eq122207 : (σ (M.op x y)) = (M.op (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ x)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1469 eq122203
    | (have j1 := eq1469 (σ (M.op x y)) x (σ x)
       grind)
    | exact resolve eq122203 eq1469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1469 eq122203
  have eq122213 : (σ (M.op x y)) = (M.op (M.op x (σ x)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23836 eq122207
    | (have j1 := eq23836 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq122207 eq23836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23836 eq122207
  have eq122217 : (σ (M.op x y)) = (M.op (M.op x (σ x)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23810 eq122213
    | exact resolve eq122213 eq23810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122213
  have eq122220 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24125 eq122217
    | exact resolve eq122217 eq24125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122217
  have eq122221 : (σ (M.op x y)) = (M.op x (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23810 eq122220
    | exact resolve eq122220 eq23810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23810 eq122220
  have eq122222 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24125 eq122221
    | exact resolve eq122221 eq24125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24125 eq122221
  have eq122223 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq122222
    | exact resolve eq122222 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122222
  have eq122224 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq122223
       have r₂ := eq27
       grind)
    | exact resolve eq122223 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122223
  have eq122225 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24207 eq122224
    | exact resolve eq122224 eq24207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122224
  have eq124924 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122225 eq27398
    | exact resolve eq27398 eq122225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27398
  have eq124926 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122225 eq28
    | (have j0 := eq28 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq28 (σ x) (σ (M.op x y))
       have r₂ := eq122225
       grind)
    | (have r₁ := eq28 y x
       have r₂ := eq122225
       grind)
    | exact resolve eq28 eq122225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq122225
  have eq124941 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq124926
  have eq124942 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq124924
  have eq124956 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq24037 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq124941
       have r₂ := eq24037 (σ (M.op x y)) x
       grind)
    | exact resolve eq124941 eq24037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24037 eq124941
  have eq124973 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122191 eq124956
    | exact resolve eq124956 eq122191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122191 eq124956
  have eq124996 : (M.op x y) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq124973 eq29
    | exact resolve eq29 eq124973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq125069 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq124996
    | exact resolve eq124996 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124996
  have eq127089 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq124973 eq124942
    | exact resolve eq124942 eq124973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124942
  have eq127120 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq127089
  have eq127135 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq127120
    | exact resolve eq127120 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127120
  have eq129776 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq127135 eq27
    | exact resolve eq27 eq127135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127135
  have eq129925 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq129776
       have r₂ := eq124973
       grind)
    | exact resolve eq129776 eq124973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124973 eq129776
  have eq129960 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq129925 eq32
    | exact resolve eq32 eq129925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq129925
  have eq130111 : x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq129960
    | exact resolve eq129960 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129960
  have eq130157 : y = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24207 eq130111
    | exact resolve eq130111 eq24207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24207 eq130111
  have eq130199 : (M.op x y) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq125069 eq130157
    | exact resolve eq130157 eq125069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125069 eq130157
  have eq130225 : x = (M.op x y) := by
    first
    | (have r₁ := eq130199
       have r₂ := eq24247
       grind)
    | exact resolve eq130199 eq24247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24247 eq130199
  have eq130246 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq130225
       grind)
    | exact superpose eq130225 eq22
    | exact resolve eq22 eq130225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq130328 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq130246 eq20
    | exact resolve eq20 eq130246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130246
  have eq130439 : (σ x) ≠ (σ x) ∨ x = (σ x) := by
    first
    | exact superpose eq130328 eq23731
    | (have r₁ := eq23731
       have r₂ := eq130328
       grind)
    | exact resolve eq23731 eq130328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23731
  have eq130465 : x = (σ x) := by grind
  clear eq130439
  have eq130466 : (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq130465
       have i₂ := eq130225
       grind)
    | exact superpose eq130225 eq130465
    | exact resolve eq130465 eq130225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130465
  have eq130485 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq130466 eq26
    | exact resolve eq26 eq130466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq130486 : x = (τ (M.op x y)) := by
    first
    | exact superpose eq130466 eq30
    | exact resolve eq30 eq130466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq130543 : ∀ X0 : G, (M.op X0 X0) = (σ (σ (σ (M.op x y)))) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq130466 eq23467
    | exact resolve eq23467 eq130466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23467
  have eq130631 : y = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq130466 eq34478
    | exact resolve eq34478 eq130466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34478
  have eq130709 : ∀ X0 : G, (M.op X0 X0) = (σ (σ (σ (M.op x y)))) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq130543
    | (have j0 := eq130543 X0
       grind)
    | exact resolve eq130543 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130543
  have eq130748 : (M.op x y) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq130486
       have i₂ := eq130225
       grind)
    | exact superpose eq130225 eq130486
    | exact resolve eq130486 eq130225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130225 eq130486
  have eq130779 : ∀ X0 : G, (M.op X0 X0) = (σ (σ (σ x))) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq130328 eq130709
    | exact resolve eq130709 eq130328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130709
  have eq130831 : ∀ X0 : G, (M.op X0 X0) = (σ (σ (M.op x y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq130466 eq130779
    | exact resolve eq130779 eq130466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130779
  have eq130872 : ∀ X0 : G, (M.op X0 X0) = (σ (σ (M.op x y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq130831
    | (have j0 := eq130831 X0
       grind)
    | exact resolve eq130831 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130831
  have eq130894 : ∀ X0 : G, (M.op X0 X0) = (σ (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq130328 eq130872
    | exact resolve eq130872 eq130328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130872
  have eq130914 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq130466 eq130894
    | exact resolve eq130894 eq130466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130894
  have eq130928 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq130914
    | (have j0 := eq130914 X0
       grind)
    | exact resolve eq130914 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130914
  have eq130939 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq130328 eq130928
    | exact resolve eq130928 eq130328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130328 eq130928
  have eq130948 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq130466 eq130939
    | exact resolve eq130939 eq130466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130466 eq130939
  have eq130990 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq130748 eq14
    | exact resolve eq14 eq130748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130748
  have eq131003 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq130990 eq20
    | exact resolve eq20 eq130990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq130990
  have eq133160 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq130631 eq1717
    | exact resolve eq1717 eq130631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1717 eq130631
  have eq133439 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq133160 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq133160
    | (have j0 := eq133160 X0 X1
       grind)
    | exact resolve eq133160 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq133160
  have eq133635 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq130948 eq133439
    | exact resolve eq133439 eq130948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133439
  have eq133780 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq130485 eq133635
    | exact resolve eq133635 eq130485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130485 eq133635
  have eq133880 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq130948 eq133780
    | exact resolve eq133780 eq130948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130948 eq133780
  have eq133881 : (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq133880
  have eq135536 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq133881 eq27
    | exact resolve eq27 eq133881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq133881
  have eq135621 : False := by grind
  exact eq135621

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_x_y_x_pxx_pxy_Equation2146 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq174 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq16 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
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
  have eq178 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op (M.op X3 X3) X2) X1 (M.op X0 X2)
       have i₂ := eq16 X0 X3 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq337 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
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
  have eq365 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq337 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq337
    | exact resolve eq337 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq407 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq561 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq407 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq174 (σ X0)
       grind)
    | exact superpose eq174 eq407
    | exact resolve eq407 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq407
  have eq590 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq561 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq561
    | exact resolve eq561 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq701 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq176 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq176 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq176 eq176
    | exact resolve eq176 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq702 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X0 X2 (M.op (M.op X1 X1) (M.op X2 X2))
       have i₂ := eq16 X0 X1 (M.op X2 X2)
       grind)
    | exact superpose eq16 eq176
    | exact resolve eq176 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq730 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X2 ∨ (k X1 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq701 X0 X1
       grind)
    | (have i₁ := eq13 X1 X2
       have i₂ := eq701 X1 X0
       grind)
    | exact superpose eq701 eq13
    | (have j0 := eq13 X0 X2
       grind)
    | (have r₁ := eq13 X1 (M.op X0 X0)
       have r₂ := eq701 X0 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq701 X0 X1
       grind)
    | exact resolve eq13 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq736 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq701 X0 X2
       grind)
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq701 X2 X0
       grind)
    | exact superpose eq701 eq16
    | exact resolve eq16 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq741 : ∀ X0 X1 : G, (k X1 (τ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq590 X1
       have i₂ := eq701 X0 (σ X1)
       grind)
    | (have i₁ := eq590 X1
       have i₂ := eq701 (σ X1) X0
       grind)
    | exact superpose eq701 eq590
    | exact resolve eq590 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq742 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq365 X1
       have i₂ := eq701 X0 (τ X1)
       grind)
    | (have i₁ := eq365 X1
       have i₂ := eq701 (τ X1) X0
       grind)
    | exact superpose eq701 eq365
    | exact resolve eq365 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq775 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (σ (M.op X1 X1))
       have i₂ := eq742 X1 (τ X0)
       grind)
    | exact superpose eq742 eq34
    | exact resolve eq34 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq794 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq775 X0 X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq775
    | exact resolve eq775 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq828 : ∀ X0 X1 X2 : G, (M.op (k (M.op X0 X0) X1) (M.op X2 X1)) = X2 ∨ (M.op X0 X0) = X1 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X0 X1
       have i₂ := eq11 (M.op X0 X0) X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 (M.op X0 X0) X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq834 : (M.op x y) = (k x y) ∨ x = y ∨ y = (M.op x x) := by
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
  have eq835 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq843 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1178 : ∀ X0 X1 X2 : G, (k X2 (σ (M.op (M.op X0 X0) (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq365 X2
       have i₂ := eq702 (τ X2) X0 X1
       grind)
    | exact superpose eq702 eq365
    | exact resolve eq365 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365 eq702
  have eq1552 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq843 X1
       have i₂ := eq701 X0 X1
       grind)
    | (have i₁ := eq843 X0
       have i₂ := eq701 X0 X1
       grind)
    | exact superpose eq701 eq843
    | exact resolve eq843 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1564 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq701 X0 X1
       have i₂ := eq843 X0
       grind)
    | exact superpose eq843 eq701
    | (have j1 := eq843 X0
       grind)
    | exact resolve eq701 eq843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1623 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq843 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq1651 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq834
       grind)
    | exact superpose eq834 eq40
    | exact resolve eq40 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq834
  have eq1652 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1651
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1651
    | exact resolve eq1651 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1651
  have eq1654 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq1652
    | exact resolve eq1652 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1652
  have eq2236 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq701 X2 X1
       have i₂ := eq1552 X2 X0
       grind)
    | exact superpose eq1552 eq701
    | (have j1 := eq1552 X1 X0
       grind)
    | exact resolve eq701 eq1552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2321 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq742 X1 (σ (M.op X1 X1))
       have i₂ := eq1552 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq1552 eq742
    | (have j1 := eq1552 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq742 eq1552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq2322 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (M.op (M.op X1 X1) (M.op X2 X2))) ∨ (M.op X0 X0) = (σ (M.op (M.op X1 X1) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1178 X1 X2 (σ (M.op (M.op X1 X1) (M.op X2 X2)))
       have i₂ := eq1552 X0 (σ (M.op (M.op X1 X1) (M.op X2 X2)))
       grind)
    | exact superpose eq1552 eq1178
    | (have j1 := eq1552 X0 (σ (M.op (M.op X1 X1) (M.op X2 X2)))
       grind)
    | exact resolve eq1178 eq1552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178
  have eq2323 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (M.op X1 X1))) ∨ (M.op X0 X0) = (σ (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq794 (σ (σ (M.op X1 X1))) X1
       have i₂ := eq1552 X0 (σ (σ (M.op X1 X1)))
       grind)
    | exact superpose eq1552 eq794
    | (have j1 := eq1552 X0 (σ (σ (M.op X1 X1)))
       grind)
    | exact resolve eq794 eq1552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794
  have eq2327 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq741 X1 (τ (M.op X1 X1))
       have i₂ := eq1552 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq1552 eq741
    | (have j1 := eq1552 X0 (τ (M.op X1 X1))
       grind)
    | exact resolve eq741 eq1552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2335 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1552 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1552
  have eq2339 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2327 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2327
  have eq2342 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq2323 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2323
  have eq2343 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (M.op (M.op X1 X1) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2322 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2322
  have eq2344 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2321 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2321
  have eq2397 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X1 (σ (M.op X0 X0))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X1 x X2
       have i₂ := eq2344 x X0
       grind)
    | exact superpose eq2344 eq176
    | exact resolve eq176 eq2344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2399 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op X0 X0)) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq178 x
       have i₂ := eq2344 x X0
       grind)
    | exact superpose eq2344 eq178
    | exact resolve eq178 eq2344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq2457 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (σ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 (M.op X1 X1) X1 X2
       have i₂ := eq2344 (M.op X1 X1) X0
       grind)
    | exact superpose eq2344 eq176
    | exact resolve eq176 eq2344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq2650 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (τ (M.op X0 X0)) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq736 X2 X1 (M.op X1 X1)
       have i₂ := eq2339 (M.op X1 X1) X0
       grind)
    | exact superpose eq2339 eq736
    | exact resolve eq736 eq2339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736 eq2339
  have eq2810 : ∀ X0 X2 : G, (σ (M.op X2 X2)) = (σ (σ (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq2344 x X2
       have i₂ := eq2342 x X0
       grind)
    | exact superpose eq2342 eq2344
    | exact resolve eq2344 eq2342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2342
  have eq4005 : ∀ X0 X1 : G, x = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 y)) X1) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq177 x
       have i₂ := eq179 X1 X0 y x
       grind)
    | (have i₁ := eq177 (M.op y y)
       have i₂ := eq179 y y y x
       grind)
    | exact superpose eq179 eq177
    | exact resolve eq177 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq179
  have eq7696 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1623 X1
       have i₂ := eq1564 X1 X0
       grind)
    | exact superpose eq1564 eq1623
    | (have j0 := eq1623 X1
       have j1 := eq1564 X1 X1
       grind)
    | (have r₁ := eq1623 (M.op X1 X1)
       have r₂ := eq1564 (M.op X1 X1) X1
       grind)
    | exact resolve eq1623 eq1564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1564 eq1623
  have eq7715 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq7696 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7696
  have eq21382 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq1654 eq835
    | exact resolve eq835 eq1654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835 eq1654
  have eq21391 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq21382
       have r₂ := eq27
       grind)
    | exact resolve eq21382 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21382
  have eq21575 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq21391 eq741
    | exact resolve eq741 eq21391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq21688 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (τ (σ y)) (M.op X1 X1)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq21391 eq2650
    | exact resolve eq2650 eq21391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2650 eq21391
  have eq21785 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op y (M.op X1 X1)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq31 eq21688
    | exact resolve eq21688 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21688
  have eq21870 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq31 eq21575
    | exact resolve eq21575 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21575
  have eq21906 : ∀ X0 : G, (M.op X0 X0) = (M.op y (k y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq2236 eq21785
    | (have j1 := eq2236 (M.op y (k y y)) x X0
       grind)
    | exact resolve eq21785 eq2236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21785
  have eq21961 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq21870 X0
       have j1 := eq730 X0 X0 y
       grind)
    | (have r₁ := eq21870 (M.op X0 X0)
       have r₂ := eq730 X0 x (k (M.op X0 X0) y)
       grind)
    | (have r₁ := eq21870 X0
       have r₂ := eq730 x x y
       grind)
    | exact resolve eq21870 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730 eq21870
  have eq21979 : (k y y) = (M.op y (k y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq2236 eq21906
    | (have j1 := eq2236 y x x
       grind)
    | exact resolve eq21906 eq2236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2236 eq21906
  have eq22030 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq21961 eq21979
    | exact resolve eq21979 eq21961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21979
  have eq22072 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq7715 x y
       grind)
    | (have r₁ := eq22030
       have r₂ := eq7715 y y
       grind)
    | (have r₁ := eq22030
       have r₂ := eq7715 x y
       grind)
    | exact resolve eq22030 eq7715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7715 eq22030
  have eq22134 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2335 X0 y
       have i₂ := eq21961 y
       grind)
    | exact superpose eq21961 eq2335
    | (have j0 := eq2335 X0 y
       grind)
    | (have r₁ := eq2335 X0 y
       have r₂ := eq21961 y
       grind)
    | exact resolve eq2335 eq21961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2335 eq21961
  have eq22152 : ∀ X0 : G, (M.op X0 X0) = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq22134 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22134
  have eq22243 : ∀ X1 X2 : G, (M.op (M.op y X1) (M.op X2 X1)) = X2 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1 X2
    first
    | (have i₁ := eq16 X2 x X1
       have i₂ := eq22152 x
       grind)
    | exact superpose eq22152 eq16
    | exact resolve eq16 eq22152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22339 : (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2399 x
       have i₂ := eq22152 x
       grind)
    | exact superpose eq22152 eq2399
    | exact resolve eq2399 eq22152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2399
  have eq22417 : ∀ X1 : G, (σ y) = (σ (σ (M.op X1 X1))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | (have i₁ := eq2810 X1 x
       have i₂ := eq22152 x
       grind)
    | exact superpose eq22152 eq2810
    | exact resolve eq2810 eq22152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2810
  have eq22468 : ∀ X0 X1 : G, (M.op (k (M.op X0 X0) X1) y) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq828 X0 X1 X1
       have i₂ := eq22152 X1
       grind)
    | exact superpose eq22152 eq828
    | (have j0 := eq828 X0 X1 x
       grind)
    | exact resolve eq828 eq22152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq22485 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (M.op X1 y)) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq2397 X0 (σ (M.op X0 X0)) X1
       have i₂ := eq22152 (σ (M.op X0 X0))
       grind)
    | exact superpose eq22152 eq2397
    | exact resolve eq2397 eq22152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2397
  have eq22494 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2343 X0 x x
       have i₂ := eq22152 (M.op x x)
       grind)
    | exact superpose eq22152 eq2343
    | exact resolve eq2343 eq22152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2343
  have eq22506 : ∀ X0 : G, y = (σ (M.op X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2457 X0 (σ (M.op X0 X0)) (σ (M.op X0 X0))
       have i₂ := eq22152 (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))
       grind)
    | exact superpose eq22152 eq2457
    | exact resolve eq2457 eq22152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2457
  have eq22508 : x = (M.op (M.op y y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4005 y y
       have i₂ := eq22152 (M.op y y)
       grind)
    | exact superpose eq22152 eq4005
    | exact resolve eq4005 eq22152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4005
  have eq22566 : x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22072 eq22508
    | exact resolve eq22508 eq22072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22508
  have eq22568 : y = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22152 eq22506
    | exact resolve eq22506 eq22152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22506
  have eq22576 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq22494 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22494
    | (have j0 := eq22494 X0
       grind)
    | exact resolve eq22494 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22494
  have eq22582 : ∀ X1 : G, (M.op (σ y) (M.op X1 y)) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq22152 eq22485
    | exact resolve eq22485 eq22152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22485
  have eq22597 : ∀ X0 X1 : G, (M.op (k y X1) y) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq22152 eq22468
    | (have j0 := eq22468 X0 X1
       grind)
    | exact resolve eq22468 eq22152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22468
  have eq22628 : ∀ X1 : G, (σ y) = (σ (σ (M.op X1 X1))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | (have i₁ := eq22417 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22417
    | (have j0 := eq22417 X1
       grind)
    | exact resolve eq22417 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22417
  have eq22699 : (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq22339
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22339
    | exact resolve eq22339 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22339
  have eq22808 : (σ x) = (σ y) ∨ y = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq22568
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22568
    | exact resolve eq22568 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22568
  have eq22815 : ∀ X1 : G, (M.op (σ y) (M.op X1 y)) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | (have i₁ := eq22582 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22582
    | (have j0 := eq22582 X1
       grind)
    | exact resolve eq22582 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22582
  have eq22827 : ∀ X0 X1 : G, (M.op (k y X1) y) = X1 ∨ y = X1 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq22152 eq22597
    | (have j0 := eq22597 (M.op X0 X0) X1
       grind)
    | exact resolve eq22597 eq22152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22597
  have eq22850 : (σ y) = (σ (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22152 eq22628
    | exact resolve eq22628 eq22152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22628
  have eq22903 : (σ x) = (M.op y (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22152 eq22699
    | exact resolve eq22699 eq22152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22699
  have eq22963 : ∀ X1 : G, (M.op (σ y) (M.op X1 (σ y))) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq22808 eq22815
    | exact resolve eq22815 eq22808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22815
  have eq22971 : ∀ X1 : G, (M.op (k y X1) y) = X1 ∨ y = X1 ∨ (M.op y y) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq22152 eq22827
    | (have j0 := eq22827 x X1
       grind)
    | exact resolve eq22827 eq22152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22152 eq22827
  have eq22986 : (σ y) = (σ (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq22850
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22850
    | exact resolve eq22850 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22850
  have eq23021 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22808 eq22903
    | exact resolve eq22903 eq22808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22903
  have eq23061 : ∀ X1 : G, (M.op (k y X1) y) = X1 ∨ y = X1 ∨ y = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq22072 eq22971
    | (have j0 := eq22971 X1
       grind)
    | exact resolve eq22971 eq22072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22072 eq22971
  have eq23062 : ∀ X1 : G, (M.op (k y X1) y) = X1 ∨ y = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | (have j0 := eq23061 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23061
  have eq23098 : ∀ X1 : G, (M.op (k (σ y) X1) (σ y)) = X1 ∨ y = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq22808 eq23062
    | (have j0 := eq23062 X1
       grind)
    | exact resolve eq23062 eq22808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23062
  have eq23105 : ∀ X1 : G, (M.op (k (σ y) X1) (σ y)) = X1 ∨ (σ y) = X1 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq22808 eq23098
    | (have j0 := eq23098 X1
       grind)
    | exact resolve eq23098 eq22808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23098
  have eq23109 : y = (τ (σ x)) ∨ y = (σ y) ∨ x = y := by
    first
    | exact superpose eq22808 eq31
    | exact resolve eq31 eq22808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23150 : x = y ∨ y = (σ y) ∨ x = y := by
    first
    | exact superpose eq29 eq23109
    | exact resolve eq23109 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23109
  have eq23151 : y = (σ y) ∨ x = y := by grind
  clear eq23150
  have eq23180 : x ≠ (σ y) ∨ x = y := by grind
  have eq23832 : x = (M.op (σ y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq22566
       have i₂ := eq23151
       grind)
    | exact superpose eq23151 eq22566
    | exact resolve eq22566 eq23151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23849 : x = (M.op (σ y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq23832
       have r₂ := eq23180
       grind)
    | exact resolve eq23832 eq23180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23832
  have eq33490 : ∀ X0 : G, (M.op x (M.op X0 (M.op x y))) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq22566 eq22243
    | exact resolve eq22243 eq22566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22566
  have eq33989 : ∀ X0 : G, (M.op x (M.op X0 (M.op x y))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq33490 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33490
  have eq34931 : ∀ X0 : G, x = (M.op (M.op y (M.op X0 (M.op x y))) X0) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq33989 eq22243
    | exact resolve eq22243 eq33989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22243 eq33989
  have eq34932 : ∀ X0 : G, x = (M.op (M.op y (M.op X0 (M.op x y))) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq34931 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34931
  have eq34946 : ∀ X0 : G, x = (M.op (M.op (σ y) (M.op X0 (M.op x y))) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq22808 eq34932
    | exact resolve eq34932 eq22808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34932
  have eq52188 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq23105 eq22963
    | (have j1 := eq23105 (σ x)
       grind)
    | exact resolve eq22963 eq23105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22963
  have eq52205 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = X0 := by
    intro X0
    first
    | (have j0 := eq52188 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52188
  have eq54404 : x = (k (σ y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq52205 eq23849
    | (have j1 := eq52205 (σ x)
       grind)
    | exact resolve eq23849 eq52205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23849 eq52205
  have eq54482 : x = (k (σ y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by grind
  clear eq54404
  have eq54690 : (σ x) = (k (σ (σ y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq54482 eq41
    | exact resolve eq41 eq54482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq54482
  have eq54696 : (σ x) = (k (σ (σ y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq54690
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq54690
    | exact resolve eq54690 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54690
  have eq54700 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq22986 eq54696
    | exact resolve eq54696 eq22986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22986 eq54696
  have eq54705 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq54700 eq23105
    | (have j0 := eq23105 (σ (M.op x y))
       grind)
    | exact resolve eq23105 eq54700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23105 eq54700
  have eq54711 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by grind
  clear eq54705
  have eq54715 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq26 eq54711
    | exact resolve eq54711 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54711
  have eq54720 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | (have r₁ := eq54715
       have r₂ := eq27
       grind)
    | exact resolve eq54715 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54715
  have eq54726 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq54720 eq31
    | exact resolve eq31 eq54720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54720
  have eq54819 : x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq29 eq54726
    | exact resolve eq54726 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54726
  have eq54820 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by grind
  clear eq54819
  have eq54837 : (M.op x y) = (τ (σ y)) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq54820 eq28
    | exact resolve eq28 eq54820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq54820
  have eq54887 : (M.op x y) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq54837
    | exact resolve eq54837 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54837
  have eq54905 : y = (τ (M.op x y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq54887 eq31
    | exact resolve eq31 eq54887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54970 : (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq54887 eq22808
    | exact resolve eq22808 eq54887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22808
  have eq55051 : (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq54970
  have eq55149 : (σ y) = (τ (M.op x y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq23151 eq54905
    | exact resolve eq54905 eq23151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54905
  have eq55175 : (σ y) = (τ (M.op x y)) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq23151 eq55149
    | exact resolve eq55149 eq23151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55149
  have eq55209 : x = (τ (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq55051 eq29
    | exact resolve eq29 eq55051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55051
  have eq55351 : x = (τ (M.op x y)) ∨ (M.op x y) = (σ y) ∨ x = y := by
    first
    | exact superpose eq23151 eq55209
    | exact resolve eq55209 eq23151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55209
  have eq55383 : x = (σ y) ∨ (M.op x y) = (σ y) ∨ x = y := by
    first
    | exact superpose eq55175 eq55351
    | exact resolve eq55351 eq55175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55175 eq55351
  have eq55400 : (M.op x y) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq55383
       have r₂ := eq23180
       grind)
    | exact resolve eq55383 eq23180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55383
  have eq55411 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq55400 eq26
    | exact resolve eq26 eq55400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55412 : y = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq55400 eq31
    | exact resolve eq31 eq55400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq55635 : (σ y) = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq23151 eq55412
    | exact resolve eq55412 eq23151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23151 eq55412
  have eq55667 : (M.op x y) = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq55400 eq55635
    | exact resolve eq55635 eq55400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55635
  have eq55763 : x = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq55411 eq34946
    | exact resolve eq34946 eq55411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34946 eq55411
  have eq55779 : x = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq55763
  have eq55790 : x = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq23021 eq55779
    | exact resolve eq55779 eq23021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23021 eq55779
  have eq55800 : x = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22576 eq55790
    | exact resolve eq55790 eq22576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22576 eq55790
  have eq55804 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq55800
       have r₂ := eq23180
       grind)
    | exact resolve eq55800 eq23180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55800
  have eq55806 : (M.op x y) = (σ x) ∨ x = y := by
    first
    | exact superpose eq55400 eq55804
    | exact resolve eq55804 eq55400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55400 eq55804
  have eq55809 : x = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq55806 eq29
    | exact resolve eq29 eq55806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq55806
  have eq55948 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq55667 eq55809
    | exact resolve eq55809 eq55667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55667 eq55809
  have eq56031 : (M.op x y) ≠ (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq23180
       have i₂ := eq55948
       grind)
    | exact superpose eq55948 eq23180
    | exact resolve eq23180 eq55948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23180
  have eq56084 : y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq56031
       have r₂ := eq54887
       grind)
    | exact resolve eq56031 eq54887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54887 eq56031
  have eq56542 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq56084
  have eq56543 : x = y := by
    first
    | (have r₁ := eq56542
       have r₂ := eq55948
       grind)
    | exact resolve eq56542 eq55948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55948 eq56542
  have eq56553 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq56543
       grind)
    | exact superpose eq56543 eq18
    | exact resolve eq18 eq56543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq56554 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq56543
       grind)
    | exact superpose eq56543 eq24
    | exact resolve eq24 eq56543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq56543
  have eq56579 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq56554
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq56554
    | exact resolve eq56554 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq56554
  have eq56582 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq56579 eq26
    | exact resolve eq26 eq56579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq56579
  have eq56693 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq701 x X0
       have i₂ := eq56553
       grind)
    | exact superpose eq56553 eq701
    | exact resolve eq701 eq56553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56760 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq2344 X0 x
       have i₂ := eq56553
       grind)
    | exact superpose eq56553 eq2344
    | exact resolve eq2344 eq56553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2344 eq56553
  have eq56976 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq20 eq56760
    | (have j0 := eq56760 X0
       grind)
    | exact resolve eq56760 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq56760
  have eq57076 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq56976 x
       have i₂ := eq56693 x
       grind)
    | exact superpose eq56693 eq56976
    | exact resolve eq56976 eq56693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56976
  have eq57393 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq56582 eq701
    | exact resolve eq701 eq56582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701 eq56582
  have eq57726 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq57393 x
       have i₂ := eq56693 x
       grind)
    | exact superpose eq56693 eq57393
    | exact resolve eq57393 eq56693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56693 eq57393
  have eq58070 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq57726 eq27
    | exact resolve eq27 eq57726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq57726
  have eq58119 : False := by grind
  exact eq58119

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_x_y_x_pxx_pyx_Equation2146 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq174 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq16 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq337 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
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
  clear eq34
  have eq365 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq337 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq337
    | exact resolve eq337 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq407 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq561 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq407 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq174 (σ X0)
       grind)
    | exact superpose eq174 eq407
    | exact resolve eq407 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq590 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq561 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq561
    | exact resolve eq561 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq701 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq176 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq176 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq176 eq176
    | exact resolve eq176 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq702 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X0 X2 (M.op (M.op X1 X1) (M.op X2 X2))
       have i₂ := eq16 X0 X1 (M.op X2 X2)
       grind)
    | exact superpose eq16 eq176
    | exact resolve eq176 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq730 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X2 ∨ (k X1 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq701 X0 X1
       grind)
    | (have i₁ := eq13 X1 X2
       have i₂ := eq701 X1 X0
       grind)
    | exact superpose eq701 eq13
    | (have j0 := eq13 X0 X2
       grind)
    | (have r₁ := eq13 X1 (M.op X0 X0)
       have r₂ := eq701 X0 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq701 X0 X1
       grind)
    | exact resolve eq13 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq732 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq174 X1
       have i₂ := eq701 X0 X1
       grind)
    | (have i₁ := eq174 X1
       have i₂ := eq701 X1 X0
       grind)
    | exact superpose eq701 eq174
    | exact resolve eq174 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq736 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq701 X0 X2
       grind)
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq701 X2 X0
       grind)
    | exact superpose eq701 eq16
    | exact resolve eq16 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq741 : ∀ X0 X1 : G, (k X1 (τ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq590 X1
       have i₂ := eq701 X0 (σ X1)
       grind)
    | (have i₁ := eq590 X1
       have i₂ := eq701 (σ X1) X0
       grind)
    | exact superpose eq701 eq590
    | exact resolve eq590 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq742 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq365 X1
       have i₂ := eq701 X0 (τ X1)
       grind)
    | (have i₁ := eq365 X1
       have i₂ := eq701 (τ X1) X0
       grind)
    | exact superpose eq701 eq365
    | exact resolve eq365 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq824 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X2) X0) (k X0 X1)) = X1 ∨ X0 = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq834 : (M.op x y) = (k y x) ∨ x = y ∨ x = (M.op y y) := by
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
  have eq835 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq837 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1172 : ∀ X0 X1 X2 : G, (k X2 (σ (M.op (M.op X0 X0) (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq365 X2
       have i₂ := eq702 (τ X2) X0 X1
       grind)
    | exact superpose eq702 eq365
    | exact resolve eq365 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365 eq702
  have eq1270 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X0) = (M.op (M.op X2 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 (M.op X1 X1) X1 (M.op (M.op X2 X2) X0)
       have i₂ := eq736 (M.op X1 X1) X2 X0
       grind)
    | exact superpose eq736 eq176
    | exact resolve eq176 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1546 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq837 X1
       have i₂ := eq701 X0 X1
       grind)
    | (have i₁ := eq837 X0
       have i₂ := eq701 X0 X1
       grind)
    | exact superpose eq701 eq837
    | exact resolve eq837 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1558 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq701 X0 X1
       have i₂ := eq837 X0
       grind)
    | exact superpose eq837 eq701
    | (have j1 := eq837 X0
       grind)
    | exact resolve eq701 eq837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1563 : ∀ X0 X1 : G, (k X1 (k X0 X0)) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq732 X0 X1
       have i₂ := eq837 X0
       grind)
    | exact superpose eq837 eq732
    | (have j1 := eq837 X0
       grind)
    | exact resolve eq732 eq837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1617 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq837 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837
  have eq1645 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq834
       grind)
    | exact superpose eq834 eq39
    | exact resolve eq39 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834
  have eq1646 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1645
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1645
    | exact resolve eq1645 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1645
  have eq1648 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq1646
    | exact resolve eq1646 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1646
  have eq2230 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq701 X2 X1
       have i₂ := eq1546 X2 X0
       grind)
    | exact superpose eq1546 eq701
    | (have j1 := eq1546 X1 X0
       grind)
    | exact resolve eq701 eq1546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2315 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq742 X1 (σ (M.op X1 X1))
       have i₂ := eq1546 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq1546 eq742
    | (have j1 := eq1546 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq742 eq1546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq2316 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (M.op (M.op X1 X1) (M.op X2 X2))) ∨ (M.op X0 X0) = (σ (M.op (M.op X1 X1) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1172 X1 X2 (σ (M.op (M.op X1 X1) (M.op X2 X2)))
       have i₂ := eq1546 X0 (σ (M.op (M.op X1 X1) (M.op X2 X2)))
       grind)
    | exact superpose eq1546 eq1172
    | (have j1 := eq1546 X0 (σ (M.op (M.op X1 X1) (M.op X2 X2)))
       grind)
    | exact resolve eq1172 eq1546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172
  have eq2329 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1546 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2337 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (M.op (M.op X1 X1) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2316 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2316
  have eq2338 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2315 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2315
  have eq2451 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (σ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 (M.op X1 X1) X1 X2
       have i₂ := eq2338 (M.op X1 X1) X0
       grind)
    | exact superpose eq2338 eq176
    | exact resolve eq176 eq2338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq7597 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1617 X1
       have i₂ := eq1558 X1 X0
       grind)
    | exact superpose eq1558 eq1617
    | (have j0 := eq1617 X1
       have j1 := eq1558 X1 X1
       grind)
    | (have r₁ := eq1617 (M.op X1 X1)
       have r₂ := eq1558 (M.op X1 X1) X1
       grind)
    | exact resolve eq1617 eq1558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1558 eq1617
  have eq7616 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq7597 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7597
  have eq16482 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq1648 eq835
    | exact resolve eq835 eq1648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835
  have eq16491 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq16482
       have r₂ := eq27
       grind)
    | exact resolve eq16482 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16482
  have eq16526 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq16491 eq741
    | exact resolve eq741 eq16491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741 eq16491
  have eq16764 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq29 eq16526
    | exact resolve eq16526 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16526
  have eq16837 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq16764 X0
       have j1 := eq730 X0 X0 x
       grind)
    | (have r₁ := eq16764 (M.op X0 X0)
       have r₂ := eq730 X0 x (k (M.op X0 X0) x)
       grind)
    | (have r₁ := eq16764 X0
       have r₂ := eq730 y x x
       grind)
    | exact resolve eq16764 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16764
  have eq16981 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = x ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2329 X0 x
       have i₂ := eq16837 x
       grind)
    | exact superpose eq16837 eq2329
    | (have j0 := eq2329 X0 x
       grind)
    | (have r₁ := eq2329 X0 x
       have r₂ := eq16837 x
       grind)
    | exact resolve eq2329 eq16837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16837
  have eq16998 : ∀ X0 : G, (M.op X0 X0) = x ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq16981 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16981
  have eq17083 : ∀ X1 X2 : G, (M.op (M.op x X1) (M.op X2 X1)) = X2 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1 X2
    first
    | (have i₁ := eq16 X2 x X1
       have i₂ := eq16998 x
       grind)
    | exact superpose eq16998 eq16
    | exact resolve eq16 eq16998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17290 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2337 X0 x x
       have i₂ := eq16998 (M.op x x)
       grind)
    | exact superpose eq16998 eq2337
    | exact resolve eq2337 eq16998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2337
  have eq17302 : ∀ X0 : G, x = (σ (M.op X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2451 X0 (σ (M.op X0 X0)) (σ (M.op X0 X0))
       have i₂ := eq16998 (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))
       grind)
    | exact superpose eq16998 eq2451
    | exact resolve eq2451 eq16998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2451
  have eq17357 : x = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq16998 eq17302
    | exact resolve eq17302 eq16998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17302
  have eq17365 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq17290 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17290
    | (have j0 := eq17290 X0
       grind)
    | exact resolve eq17290 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17290
  have eq17557 : (σ x) = (σ y) ∨ x = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq17357
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17357
    | exact resolve eq17357 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17357
  have eq17802 : y = (τ (σ x)) ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq17557 eq31
    | exact resolve eq31 eq17557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17557
  have eq17839 : x = y ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq29 eq17802
    | exact resolve eq17802 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17802
  have eq17840 : x = (σ x) ∨ x = y := by grind
  clear eq17839
  have eq17841 : (M.op x y) = (M.op (σ x) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq17840
       grind)
    | exact superpose eq17840 eq18
    | exact resolve eq18 eq17840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17842 : (σ x) = (σ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq17840
       grind)
    | exact superpose eq17840 eq22
    | exact resolve eq22 eq17840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17844 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (σ x))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq17840
       grind)
    | exact superpose eq17840 eq39
    | exact resolve eq39 eq17840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq19723 : (σ (σ (M.op x y))) = (k (σ (σ y)) (σ x)) ∨ x = y ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq1648 eq17844
    | exact resolve eq17844 eq1648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1648 eq17844
  have eq19749 : (σ (σ (M.op x y))) = (k (σ (σ y)) (σ x)) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq19723
  have eq19773 : (σ (σ (M.op x y))) = (k (σ (σ y)) (σ x)) ∨ x = y ∨ (σ x) = (M.op y y) := by
    first
    | exact superpose eq17840 eq19749
    | exact resolve eq19749 eq17840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19749
  have eq19774 : (σ (σ (M.op x y))) = (k (σ (σ x)) (σ x)) ∨ x = y ∨ (σ x) = (M.op y y) := by
    first
    | exact superpose eq17365 eq19773
    | (have j1 := eq17365 y
       grind)
    | exact resolve eq19773 eq17365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17365 eq19773
  have eq19775 : (k (σ x) (σ x)) = (σ (σ (M.op x y))) ∨ x = y ∨ (σ x) = (M.op y y) := by
    first
    | exact superpose eq17842 eq19774
    | exact resolve eq19774 eq17842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19774
  have eq23664 : (k x x) = (τ (σ (σ (M.op x y)))) ∨ x = y ∨ (σ x) = (M.op y y) := by
    first
    | exact superpose eq19775 eq97
    | exact resolve eq97 eq19775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19775
  have eq23690 : (σ (M.op x y)) = (k x x) ∨ x = y ∨ (σ x) = (M.op y y) := by
    first
    | (have i₁ := eq23664
       have i₂ := eq15 sF1
       grind)
    | exact superpose eq15 eq23664
    | exact resolve eq23664 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23664
  have eq23697 : (σ x) = (M.op y y) ∨ x = y ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq17840 eq23690
    | exact resolve eq23690 eq17840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23690
  have eq24147 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq701 y X0
       have i₂ := eq23697
       grind)
    | exact superpose eq23697 eq701
    | exact resolve eq701 eq23697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24151 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq732 y X0
       have i₂ := eq23697
       grind)
    | exact superpose eq23697 eq732
    | exact resolve eq732 eq23697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732 eq23697
  have eq24639 : ∀ X0 : G, (τ (σ (M.op x y))) = (k x x) ∨ x = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq24147 eq97
    | (have j1 := eq24147 X0
       grind)
    | exact resolve eq97 eq24147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq24645 : ∀ X0 X1 : G, (k X0 (σ (M.op x y))) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq24147 eq1563
    | (have j0 := eq1563 (σ x) X1
       have j1 := eq24147 (σ x)
       grind)
    | exact resolve eq1563 eq24147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24147
  have eq24661 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 (σ (M.op x y))) = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq24645 X0 (σ x)
       have j1 := eq7616 X0 (σ x)
       grind)
    | (have r₁ := eq24645 (M.op X0 X0) x
       have r₂ := eq7616 X0 (k (M.op X0 X0) (σ (M.op x y)))
       grind)
    | (have r₁ := eq24645 X0 x
       have r₂ := eq7616 (σ x) (σ x)
       grind)
    | (have r₁ := eq24645 X0 X0
       have r₂ := eq7616 X0 (σ x)
       grind)
    | exact resolve eq24645 eq7616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24645
  have eq24666 : ∀ X0 : G, (M.op x y) = (k x x) ∨ x = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq28 eq24639
    | (have j0 := eq24639 X0
       grind)
    | exact resolve eq24639 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24639
  have eq24672 : ∀ X0 : G, (M.op x y) = (k (σ x) (σ x)) ∨ x = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq17840 eq24666
    | (have j0 := eq24666 X0
       grind)
    | exact resolve eq24666 eq17840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24666
  have eq25872 : ∀ X0 X1 : G, (k X1 (σ (M.op x y))) = X1 ∨ (M.op X0 X0) = (σ x) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq701 X0 X1
       have i₂ := eq24661 (M.op X0 X0)
       grind)
    | exact superpose eq24661 eq701
    | (have j1 := eq24661 X1
       grind)
    | exact resolve eq701 eq24661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25878 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (σ x)) = X1 ∨ (k X2 (σ (M.op x y))) = X2 ∨ x = y := by
    intro X0 X1 X2
    first
    | (have i₁ := eq736 X0 X1 X2
       have i₂ := eq24661 (M.op X0 X0)
       grind)
    | exact superpose eq24661 eq736
    | (have j1 := eq24661 X2
       grind)
    | exact resolve eq736 eq24661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq25923 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (σ x) X1) ∨ (k X2 (σ (M.op x y))) = X2 ∨ x = y := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1270 X0 X1 X2
       have i₂ := eq24661 (M.op X2 X2)
       grind)
    | exact superpose eq24661 eq1270
    | (have j1 := eq24661 X2
       grind)
    | exact resolve eq1270 eq24661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1270 eq24661
  have eq26135 : ∀ X1 X2 : G, (M.op (M.op (σ x) X1) (σ x)) = X1 ∨ (k X2 (σ (M.op x y))) = X2 ∨ x = y := by
    intro X1 X2
    first
    | exact superpose eq25923 eq25878
    | (have j0 := eq25878 x X1 X2
       have j1 := eq25923 x X1 X2
       grind)
    | exact resolve eq25878 eq25923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25878 eq25923
  have eq26361 : ∀ X0 X1 : G, (M.op x y) = (σ (M.op x y)) ∨ x = y ∨ (k X0 (σ x)) = X0 ∨ x = y ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq24672 eq24151
    | (have j0 := eq24151 X0
       have j1 := eq24672 X1
       grind)
    | exact resolve eq24151 eq24672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24151
  have eq26368 : ∀ X0 X1 : G, (k X0 (M.op x y)) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq24672 eq1563
    | (have j0 := eq1563 (σ x) X1
       have j1 := eq24672 (σ x)
       grind)
    | exact resolve eq1563 eq24672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1563 eq24672
  have eq26378 : ∀ X0 X1 : G, (M.op x y) = (σ (M.op x y)) ∨ x = y ∨ (k X0 (σ x)) = X0 ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | (have j0 := eq26361 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26361
  have eq26390 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 (M.op x y)) = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq26368 X0 (σ x)
       have j1 := eq7616 X0 (σ x)
       grind)
    | (have r₁ := eq26368 (M.op X0 X0) x
       have r₂ := eq7616 X0 (k (M.op X0 X0) (M.op x y))
       grind)
    | (have r₁ := eq26368 X0 x
       have r₂ := eq7616 (σ x) (σ x)
       grind)
    | (have r₁ := eq26368 X0 X0
       have r₂ := eq7616 X0 (σ x)
       grind)
    | exact resolve eq26368 eq7616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7616 eq26368
  have eq26395 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = y ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq26378 X0 x
       have j1 := eq730 X0 X0 (σ x)
       grind)
    | (have r₁ := eq26378 (M.op X0 X0) x
       have r₂ := eq730 X0 x (k (M.op X0 X0) (σ x))
       grind)
    | (have r₁ := eq26378 X0 X0
       have r₂ := eq730 X0 x (σ x)
       grind)
    | exact resolve eq26378 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26378
  have eq26423 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (σ x) ∨ x = y ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq26395 eq2329
    | (have j0 := eq2329 X0 (σ x)
       grind)
    | (have r₁ := eq2329 X0 (σ x)
       have r₂ := eq26395 (σ x)
       grind)
    | exact resolve eq2329 eq26395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26395
  have eq26459 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ x = y ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq26423 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26423
  have eq26748 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (σ x)) = X1 ∨ x = y ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X1
       have i₂ := eq26459 X1
       grind)
    | exact superpose eq26459 eq16
    | exact resolve eq16 eq26459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26898 : ∀ X1 : G, (M.op (M.op (σ x) X1) (σ x)) = X1 ∨ x = y ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X1
    first
    | exact superpose eq26459 eq26748
    | exact resolve eq26748 eq26459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26748
  have eq30000 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 X0) = (σ (M.op x y)) ∨ (M.op X1 X1) = (σ x) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq25872 eq2329
    | (have j0 := eq2329 X0 (σ (M.op x y))
       have j1 := eq25872 X1 X1
       grind)
    | (have r₁ := eq2329 X0 (σ (M.op x y))
       have r₂ := eq25872 X0 (σ (M.op x y))
       grind)
    | exact resolve eq2329 eq25872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25872
  have eq30027 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ (M.op X1 X1) = (σ x) ∨ x = y := by
    intro X0 X1
    first
    | (have j0 := eq30000 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30000
  have eq30048 : ∀ X0 X1 : G, (M.op X1 X1) = (σ x) ∨ (M.op X0 X0) = (M.op x y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq26459 eq30027
    | (have j0 := eq30027 X0 X1
       have j1 := eq26459 X1
       grind)
    | exact resolve eq30027 eq26459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26459 eq30027
  have eq30139 : ∀ X0 X1 : G, (σ x) = (k X0 X0) ∨ (σ x) = X0 ∨ (k X1 (M.op x y)) = X1 ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq1546 X0 X1
       have i₂ := eq26390 (M.op X0 X0)
       grind)
    | exact superpose eq26390 eq1546
    | (have j1 := eq26390 X1
       grind)
    | exact resolve eq1546 eq26390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1546
  have eq31145 : ∀ X0 : G, (M.op x y) ≠ (σ x) ∨ (M.op X0 X0) = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq30048 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30048
  have eq32379 : y = (M.op (M.op x y) (σ x)) ∨ x = y ∨ (M.op x y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq17841 eq26898
    | exact resolve eq26898 eq17841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26898
  have eq32432 : y = (M.op (M.op x y) (σ x)) ∨ x = y ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq32379
  have eq39606 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq17083 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17083
    | (have j0 := eq17083 y X0
       grind)
    | exact resolve eq17083 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17083
  have eq48418 : ∀ X0 : G, y = (M.op (M.op x y) (σ x)) ∨ (k X0 (σ (M.op x y))) = X0 ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq17841 eq26135
    | (have j0 := eq26135 x X0
       grind)
    | exact resolve eq26135 eq17841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17841 eq26135
  have eq48497 : ∀ X0 : G, y = (M.op (M.op x y) (σ x)) ∨ (k X0 (σ (M.op x y))) = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq48418 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48418
  have eq48531 : ∀ X0 : G, y = (M.op (M.op x y) (σ x)) ∨ (k X0 (M.op x y)) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq32432 eq48497
    | exact resolve eq48497 eq32432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32432 eq48497
  have eq48605 : ∀ X0 : G, y = (k (σ x) (M.op x y)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ x)) ∨ (k X0 (M.op x y)) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq11 X0 x
       have i₂ := eq48531 (M.op x X0)
       grind)
    | exact superpose eq48531 eq11
    | (have j0 := eq11 y (k (σ x) (M.op x y))
       have j1 := eq48531 X0
       grind)
    | exact resolve eq11 eq48531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48531
  have eq48629 : ∀ X0 : G, y = (k (σ x) (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ x)) ∨ (k X0 (M.op x y)) = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq48605 X0
       have j1 := eq31145 (σ x)
       grind)
    | (have r₁ := eq48605 X0
       have r₂ := eq31145 X0
       grind)
    | exact resolve eq48605 eq31145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48605
  have eq48636 : ∀ X0 : G, y = (k (σ x) (M.op x y)) ∨ (k X0 (M.op x y)) = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq48629 X0
       have j1 := eq730 X0 X0 (M.op x y)
       grind)
    | (have r₁ := eq48629 X0
       have r₂ := eq730 (σ x) x (M.op x y)
       grind)
    | (have r₁ := eq48629 (M.op X0 X0)
       have r₂ := eq730 X0 x (k (M.op X0 X0) (M.op x y))
       grind)
    | exact resolve eq48629 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730 eq48629
  have eq48646 : ∀ X0 : G, (σ y) = (k (σ (σ x)) (σ (M.op x y))) ∨ (k X0 (M.op x y)) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq48636 (k X0 sF0)
       grind)
    | exact superpose eq48636 eq41
    | (have j1 := eq48636 X0
       grind)
    | exact resolve eq41 eq48636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq48636
  have eq48653 : ∀ X0 : G, (σ y) = (k (σ (σ x)) (σ (M.op x y))) ∨ (k X0 (M.op x y)) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq48646 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48646
    | (have j0 := eq48646 X0
       grind)
    | exact resolve eq48646 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48646
  have eq48657 : ∀ X0 : G, (σ y) = (k (σ x) (σ (M.op x y))) ∨ (k X0 (M.op x y)) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq17842 eq48653
    | (have j0 := eq48653 X0
       grind)
    | exact resolve eq48653 eq17842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48653
  have eq48667 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (M.op X0 X0) (σ x)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (k X1 (M.op x y)) = X1 ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq824 X0 X1 x
       have i₂ := eq48657 (k X0 X1)
       grind)
    | exact superpose eq48657 eq824
    | (have j0 := eq824 (σ (M.op x y)) (M.op (M.op (M.op X0 X0) (σ x)) (σ y)) x
       have j1 := eq48657 X1
       grind)
    | exact resolve eq824 eq48657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824 eq48657
  have eq48671 : ∀ X1 : G, (σ (M.op x y)) = (M.op (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ x)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (k X1 (M.op x y)) = X1 ∨ x = y := by
    intro X1
    first
    | exact superpose eq2230 eq48667
    | (have j0 := eq48667 x X1
       have j1 := eq2230 (σ (M.op x y)) X1 (σ x)
       grind)
    | exact resolve eq48667 eq2230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2230 eq48667
  have eq48675 : ∀ X1 : G, (σ (M.op x y)) = (M.op (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ x)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (k X1 (M.op x y)) = X1 ∨ x = y := by
    intro X1
    first
    | exact superpose eq26390 eq48671
    | (have j0 := eq48671 X1
       have j1 := eq26390 X1
       grind)
    | exact resolve eq48671 eq26390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48671
  have eq48676 : ∀ X1 : G, (σ (M.op x y)) = (M.op (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ x)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (k X1 (M.op x y)) = X1 ∨ x = y := by
    intro X1
    first
    | (have j0 := eq48675 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48675
  have eq48680 : ∀ X1 : G, (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (k X1 (M.op x y)) = X1 ∨ x = y := by
    intro X1
    first
    | exact superpose eq30139 eq48676
    | (have j0 := eq48676 X1
       have j1 := eq30139 (σ (M.op x y)) X1
       grind)
    | exact resolve eq48676 eq30139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30139 eq48676
  have eq48683 : ∀ X1 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (k X1 (M.op x y)) = X1 ∨ x = y := by
    intro X1
    first
    | exact superpose eq26390 eq48680
    | (have j0 := eq48680 X1
       have j1 := eq26390 X1
       grind)
    | exact resolve eq48680 eq26390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26390 eq48680
  have eq48684 : ∀ X1 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (k X1 (M.op x y)) = X1 ∨ x = y := by
    intro X1
    first
    | exact superpose eq26 eq48683
    | (have j0 := eq48683 X1
       grind)
    | exact resolve eq48683 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48683
  have eq48685 : ∀ X1 : G, (k X1 (M.op x y)) = X1 ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    intro X1
    first
    | (have j0 := eq48684 X1
       grind)
    | (have r₁ := eq48684 X1
       have r₂ := eq27
       grind)
    | exact resolve eq48684 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48684
  have eq49010 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op X0 X0) = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq48685 eq2329
    | (have j0 := eq2329 X0 (M.op x y)
       grind)
    | (have r₁ := eq2329 X0 (M.op x y)
       have r₂ := eq48685 (M.op x y)
       grind)
    | exact resolve eq2329 eq48685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2329 eq48685
  have eq49067 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq49010 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49010
  have eq49410 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq39606 y
       have i₂ := eq49067 y
       grind)
    | exact superpose eq49067 eq39606
    | exact resolve eq39606 eq49067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49067
  have eq49517 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq49410
  have eq49619 : x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq16998 eq49517
    | exact resolve eq49517 eq16998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49517
  have eq49620 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq49619
  have eq50160 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq49620 eq31
    | exact resolve eq31 eq49620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq49620
  have eq50217 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq29 eq50160
    | exact resolve eq50160 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50160
  have eq50218 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq50217
  have eq50239 : (M.op x y) = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq50218 eq28
    | exact resolve eq28 eq50218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq50218
  have eq50322 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq50239
    | exact resolve eq50239 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq50239
  have eq50344 : (M.op x y) = (σ x) ∨ y = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq50322
       have i₂ := eq17840
       grind)
    | exact superpose eq17840 eq50322
    | exact resolve eq50322 eq17840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50399 : (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq17840
       have i₂ := eq50322
       grind)
    | exact superpose eq50322 eq17840
    | exact resolve eq17840 eq50322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17840 eq50322
  have eq50435 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ x) ∨ x = y := by
    first
    | exact superpose eq50399 eq50344
    | exact resolve eq50344 eq50399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50344 eq50399
  have eq50436 : (M.op x y) = (σ x) ∨ x = y := by grind
  clear eq50435
  have eq50479 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq50436 eq26
    | exact resolve eq26 eq50436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50535 : (M.op x y) = (σ (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq50436 eq17842
    | exact resolve eq17842 eq50436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17842
  have eq50574 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op X0 X0) = (M.op x y) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq50436 eq31145
    | (have j0 := eq31145 X0
       grind)
    | (have r₁ := eq31145 X0
       have r₂ := eq50436
       grind)
    | exact resolve eq31145 eq50436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31145
  have eq50613 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op X0 X0) = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq50574 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50574
  have eq50614 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq50613 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50613
  have eq50656 : (M.op x y) = (σ (M.op x y)) ∨ x = y := by grind
  clear eq50535
  have eq50707 : (M.op x y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq20 eq50656
    | exact resolve eq50656 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50656
  have eq52583 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq39606 y
       have i₂ := eq50614 y
       grind)
    | exact superpose eq50614 eq39606
    | exact resolve eq39606 eq50614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39606
  have eq52692 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq52583
  have eq52801 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq16998 eq52692
    | exact resolve eq52692 eq16998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16998 eq52692
  have eq52802 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq52801
  have eq53070 : (M.op x y) = (σ y) ∨ x = y := by
    first
    | exact superpose eq50436 eq52802
    | exact resolve eq52802 eq50436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50436 eq52802
  have eq53654 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq53070 eq50479
    | exact resolve eq50479 eq53070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50479 eq53070
  have eq53655 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by grind
  clear eq53654
  have eq53675 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq50614 eq53655
    | exact resolve eq53655 eq50614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50614 eq53655
  have eq53768 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq53675 eq27
    | exact resolve eq27 eq53675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53675
  have eq53836 : x = y := by
    first
    | (have r₁ := eq53768
       have r₂ := eq50707
       grind)
    | exact resolve eq53768 eq50707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50707 eq53768
  have eq53855 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq53836
       grind)
    | exact superpose eq53836 eq18
    | exact resolve eq18 eq53836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq53856 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq53836
       grind)
    | exact superpose eq53836 eq24
    | exact resolve eq24 eq53836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq53836
  have eq53879 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq53856
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq53856
    | exact resolve eq53856 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq53856
  have eq53881 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq53879 eq26
    | exact resolve eq26 eq53879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq53879
  have eq53964 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq701 x X0
       have i₂ := eq53855
       grind)
    | exact superpose eq53855 eq701
    | exact resolve eq701 eq53855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54029 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq2338 X0 x
       have i₂ := eq53855
       grind)
    | exact superpose eq53855 eq2338
    | exact resolve eq2338 eq53855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2338 eq53855
  have eq54191 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq20 eq54029
    | (have j0 := eq54029 X0
       grind)
    | exact resolve eq54029 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq54029
  have eq54277 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq54191 x
       have i₂ := eq53964 x
       grind)
    | exact superpose eq53964 eq54191
    | exact resolve eq54191 eq53964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54191
  have eq54597 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq53881 eq701
    | exact resolve eq701 eq53881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701 eq53881
  have eq54871 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54597 x
       have i₂ := eq53964 x
       grind)
    | exact superpose eq53964 eq54597
    | exact resolve eq54597 eq53964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53964 eq54597
  have eq55153 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq54871 eq27
    | exact resolve eq27 eq54871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq54871
  have eq55190 : False := by grind
  exact eq55190
