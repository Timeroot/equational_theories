import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2452`: `x = (x ◇ ((x ◇ y) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pxy_pyx_Equation2452 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2452 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2452.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq627 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq630 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq658 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq630 x y
       grind)
    | exact superpose eq630 eq16
    | (have j1 := eq630 y x
       grind)
    | exact resolve eq16 eq630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq3649 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq627 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq627
    | exact resolve eq627 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq3709 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3649 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3649
    | (have j0 := eq3649 X0 X1
       grind)
    | exact resolve eq3649 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3649
  have eq16715 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq658
       have i₂ := eq3709 x y
       grind)
    | exact superpose eq3709 eq658
    | (have j1 := eq3709 (σ x) (σ y)
       grind)
    | (have r₁ := eq658
       have r₂ := eq3709 x y
       grind)
    | (have r₁ := eq658
       have r₂ := eq3709 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq658
       have r₂ := eq3709 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq658 eq3709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3709
  have eq16716 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq16715
  have eq232504 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16716
       grind)
    | exact superpose eq16716 eq16
    | exact resolve eq16 eq16716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16716
  have eq232505 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq232504
       have r₂ := eq22 x
       grind)
    | exact resolve eq232504 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232504
  have eq232507 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq232505
       grind)
    | exact superpose eq232505 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq232505
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq232505
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq232505
       grind)
    | exact resolve eq13 eq232505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232505
  have eq232539 : x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq232507
  have eq235190 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq232539
       grind)
    | exact superpose eq232539 eq16
    | exact resolve eq16 eq232539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232539
  have eq235191 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq235190
       have r₂ := eq22 x
       grind)
    | exact resolve eq235190 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235190
  have eq235192 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq658
       have i₂ := eq235191
       grind)
    | exact superpose eq235191 eq658
    | exact resolve eq658 eq235191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658 eq235191
  have eq235219 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq235192
  have eq235220 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq235219
  have eq235232 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq235220
       grind)
    | exact superpose eq235220 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq235220
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq235220
       grind)
    | exact resolve eq13 eq235220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235233 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq235220
       grind)
    | exact superpose eq235220 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq235220
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq235220
       grind)
    | exact resolve eq13 eq235220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235220
  have eq235263 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq235233
  have eq235264 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq235263
  have eq235265 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq235232
  have eq235266 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq235265
  have eq235272 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq235264
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq235264
    | exact resolve eq235264 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235264
  have eq235273 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq235266
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq235266
    | exact resolve eq235266 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235266
  have eq235278 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq235272
       grind)
    | exact superpose eq235272 eq16
    | exact resolve eq16 eq235272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235369 : (σ (k y x)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq235272
       have i₂ := eq235273
       grind)
    | exact superpose eq235273 eq235272
    | exact resolve eq235272 eq235273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235272 eq235273
  have eq235434 : (σ x) = (σ y) ∨ (σ (k y x)) = (σ (k x y)) := by grind
  clear eq235369
  have eq235471 : y = (τ (σ x)) ∨ (σ (k y x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq235434
       grind)
    | exact superpose eq235434 eq10
    | exact resolve eq10 eq235434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235434
  have eq235775 : x = y ∨ (σ (k y x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq235471
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq235471
    | exact resolve eq235471 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235471
  have eq235777 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq235775
       grind)
    | exact superpose eq235775 eq16
    | exact resolve eq16 eq235775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235775
  have eq235778 : (σ (k y x)) = (σ (k x y)) := by
    first
    | (have r₁ := eq235777
       have r₂ := eq22 x
       grind)
    | exact resolve eq235777 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235777
  have eq235799 : (k y x) = (τ (σ (k x y))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq235778
       grind)
    | exact superpose eq235778 eq10
    | exact resolve eq10 eq235778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235778
  have eq236105 : (k y x) = (k x y) := by
    first
    | (have i₁ := eq235799
       have i₂ := eq10 (k x y)
       grind)
    | exact superpose eq10 eq235799
    | exact resolve eq235799 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235799
  have eq236111 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq236105
       grind)
    | exact superpose eq236105 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq236105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236105
  have eq236169 : x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq236111
       have r₂ := eq13 x y
       grind)
    | (have r₁ := eq236111
       have r₂ := eq13 y x
       grind)
    | exact resolve eq236111 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236111
  have eq236208 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq236169
       grind)
    | exact superpose eq236169 eq16
    | exact resolve eq16 eq236169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236169
  have eq236209 : (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq236208
       have r₂ := eq22 x
       grind)
    | exact resolve eq236208 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236208
  have eq236217 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq235278
       have i₂ := eq236209
       grind)
    | exact superpose eq236209 eq235278
    | exact resolve eq235278 eq236209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235278 eq236209
  have eq236265 : (σ x) = (σ y) := by grind
  clear eq236217
  have eq236267 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq236265
       grind)
    | exact superpose eq236265 eq16
    | exact resolve eq16 eq236265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236268 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq236265
       grind)
    | exact superpose eq236265 eq10
    | exact resolve eq10 eq236265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236265
  have eq236572 : x = y := by
    first
    | (have i₁ := eq236268
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq236268
    | exact resolve eq236268 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236268
  have eq236573 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq236267
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq236267
    | exact resolve eq236267 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq236267
  have eq236574 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq236573
       have i₂ := eq236572
       grind)
    | exact superpose eq236572 eq236573
    | exact resolve eq236573 eq236572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236572 eq236573
  have eq236575 : False := by grind
  exact eq236575

/-- `Equation2473`: `x = (x ◇ ((y ◇ y) ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pxy_pyy_pyx_Equation2473 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X1) X2)) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24
    | exact resolve eq24 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op (M.op X0 X0) X1)) (M.op (M.op X0 X0) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op (M.op X0 X0) X1) X0
       have i₂ := eq9 (M.op (M.op X0 X0) X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq71 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) X2)) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op (M.op X1 X1) X2)) X1 X2
       have i₂ := eq63 X1 X2 X0
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq77 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq71 X0 X1 x
       grind)
    | exact superpose eq71 eq9
    | exact resolve eq9 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq408 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (M.op X1 X1) = (τ X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq411 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq419 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (M.op (τ X1) (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq432 : ∀ X0 : G, (τ X0) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
  have eq1023 : ∀ X0 : G, (k X0 (τ (σ (k X0 X0)))) = (τ (M.op (σ X0) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq65 x
       have i₂ := eq411 x x
       grind)
    | exact superpose eq411 eq65
    | (have j1 := eq411 X0 X0
       grind)
    | exact resolve eq65 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1025 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq1026 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq1034 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 (σ X1) (σ X0)
       have i₂ := eq411 X1 X0
       grind)
    | exact superpose eq411 eq77
    | (have j1 := eq411 X1 X0
       grind)
    | exact resolve eq77 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1036 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq411 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq1037 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1036 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036
  have eq1046 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1026 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026
  have eq1047 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1025 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025
  have eq1049 : ∀ X0 : G, (k X0 (τ (σ (k X0 X0)))) = (τ (M.op (σ X0) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1023 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023
  have eq1051 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ (k X0 X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1046 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq1046
    | (have j0 := eq1046 X0
       grind)
    | exact resolve eq1046 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1046
  have eq1052 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1047 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq1047
    | (have j0 := eq1047 X0
       grind)
    | exact resolve eq1047 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047
  have eq1053 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ (k X0 X0)))) = (k X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1049 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq1049
    | (have j0 := eq1049 X0
       grind)
    | exact resolve eq1049 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049
  have eq1060 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1037 (τ X0)
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq1037
    | (have j0 := eq1037 (τ X0)
       grind)
    | exact resolve eq1037 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037
  have eq1068 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1060 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1060
    | (have j0 := eq1060 X0
       grind)
    | exact resolve eq1060 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060
  have eq1074 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1068 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1068
    | (have j0 := eq1068 X0
       grind)
    | exact resolve eq1068 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068
  have eq3449 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (k (τ X0) (k (τ X0) (τ X0)))) = (M.op X0 (σ (k (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq1052 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1052
    | exact resolve eq1052 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052
  have eq3486 : ∀ X0 : G, (σ (k (τ X0) (k (τ X0) (τ X0)))) = (M.op X0 (k (σ (τ X0)) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3449 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq3449
    | (have j0 := eq3449 X0
       grind)
    | exact resolve eq3449 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3449
  have eq3490 : ∀ X0 : G, (σ (k (τ X0) (k (τ X0) (τ X0)))) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3486 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3486
    | (have j0 := eq3486 X0
       grind)
    | exact resolve eq3486 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3486
  have eq3491 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k X0 (σ (k (τ X0) (τ X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3490 X0
       have i₂ := eq19 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq19 eq3490
    | (have j0 := eq3490 X0
       grind)
    | exact resolve eq3490 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3490
  have eq3492 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k X0 (k (σ (τ X0)) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3491 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq3491
    | (have j0 := eq3491 X0
       grind)
    | exact resolve eq3491 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3491
  have eq3493 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3492 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3492
    | (have j0 := eq3492 X0
       grind)
    | exact resolve eq3492 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3492
  have eq3496 : ∀ X0 : G, (k (τ X0) (τ (k X0 X0))) = (M.op (τ X0) (τ (k X0 X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq3493 (τ X0)
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq3493
    | (have j0 := eq3493 (τ X0)
       grind)
    | exact resolve eq3493 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3576 : ∀ X0 : G, (M.op (τ X0) (τ (k X0 X0))) = (τ (k X0 (k X0 X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq3496 X0
       have i₂ := eq33 (k X0 X0) X0
       grind)
    | exact superpose eq33 eq3496
    | (have j0 := eq3496 X0
       grind)
    | exact resolve eq3496 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3496
  have eq4058 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ (k X0 X0)))) = (k X0 (k X0 X0)) := by
    intro X0
    grind
  clear eq1053
  have eq4076 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (τ (M.op (σ X0) (σ (k X0 X0)))) = (k X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4058 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq4058
    | (have j0 := eq4058 X0
       grind)
    | exact resolve eq4058 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4058
  have eq4263 : ∀ X0 : G, (τ X0) = (M.op (τ (k X0 (k X0 X0))) (τ (k X0 X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq77 (τ X0) (τ (k X0 X0))
       have i₂ := eq3576 X0
       grind)
    | exact superpose eq3576 eq77
    | (have j1 := eq3576 X0
       grind)
    | exact resolve eq77 eq3576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3576
  have eq4451 : ∀ X0 : G, (τ (σ X0)) = (M.op (k X0 (τ (k (σ X0) (σ X0)))) (τ (k (σ X0) (σ X0)))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq4263 (σ X0)
       have i₂ := eq30 X0 (k (σ X0) (σ X0))
       grind)
    | exact superpose eq30 eq4263
    | (have j0 := eq4263 (σ X0)
       grind)
    | exact resolve eq4263 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4263
  have eq4482 : ∀ X0 : G, (τ (σ X0)) = (M.op (k X0 (k (τ (σ X0)) X0)) (k (τ (σ X0)) X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq4451 x
       have i₂ := eq24 (σ x) x
       grind)
    | exact superpose eq24 eq4451
    | (have j0 := eq4451 X0
       grind)
    | exact resolve eq4451 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4451
  have eq4497 : ∀ X0 : G, (M.op (k X0 (k X0 X0)) (k X0 X0)) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq4482 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4482
    | (have j0 := eq4482 X0
       grind)
    | exact resolve eq4482 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4482
  have eq4511 : ∀ X0 : G, (M.op (k X0 (k X0 X0)) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4497 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4497
    | (have j0 := eq4497 X0
       grind)
    | exact resolve eq4497 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4497
  have eq6789 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq408 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq408
    | exact resolve eq408 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq6853 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6789 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq6789
    | (have j0 := eq6789 X0 X1
       grind)
    | exact resolve eq6789 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6789
  have eq6926 : ∀ X0 X1 X2 : G, (k (τ X2) (k X1 X0)) = (τ (k X2 (σ (M.op X0 X1)))) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X2 (k X1 X0)
       have i₂ := eq6853 X0 X1
       grind)
    | exact superpose eq6853 eq24
    | (have j1 := eq6853 X0 X1
       grind)
    | exact resolve eq24 eq6853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6931 : ∀ X0 X1 X2 : G, (k (k X1 X0) (τ X2)) = (τ (k (σ (M.op X0 X1)) X2)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 (k X1 X0) X2
       have i₂ := eq6853 X0 X1
       grind)
    | exact superpose eq6853 eq30
    | (have j1 := eq6853 X0 X1
       grind)
    | exact resolve eq30 eq6853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6953 : ∀ X0 X1 X2 : G, (k (k X1 X0) (τ X2)) = (k (M.op X0 X1) (τ X2)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6931 X0 X1 X2
       have i₂ := eq30 (M.op X0 X1) X2
       grind)
    | exact superpose eq30 eq6931
    | (have j0 := eq6931 X0 X1 X2
       grind)
    | exact resolve eq6931 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq6931
  have eq6958 : ∀ X0 X1 X2 : G, (k (τ X2) (k X1 X0)) = (k (τ X2) (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6926 X0 X1 X2
       have i₂ := eq24 X2 (M.op X0 X1)
       grind)
    | exact superpose eq24 eq6926
    | (have j0 := eq6926 X0 X1 X2
       grind)
    | exact resolve eq6926 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq6926
  have eq9647 : ∀ X0 X1 X2 : G, (k (k X1 X2) X0) = (k (M.op X2 X1) X0) ∨ (M.op X2 X2) = X1 ∨ (M.op X1 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6953 X0 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6953
    | (have j0 := eq6953 X2 X1 X2
       grind)
    | exact resolve eq6953 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6953
  have eq9912 : ∀ X0 X1 X2 : G, (k X0 (k X1 X2)) = (k X0 (M.op X2 X1)) ∨ (M.op X2 X2) = X1 ∨ (M.op X1 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6958 X0 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6958
    | (have j0 := eq6958 X2 X1 X2
       grind)
    | exact resolve eq6958 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6958
  have eq10139 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3493 X0
       have i₂ := eq9912 X0 X0 X0
       grind)
    | exact superpose eq9912 eq3493
    | (have j0 := eq3493 X0
       have j1 := eq9912 X0 X0 X0
       grind)
    | exact resolve eq3493 eq9912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3493
  have eq10151 : ∀ X0 : G, (M.op (k X0 (M.op X0 X0)) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4511 X0
       have i₂ := eq9912 X0 X0 X0
       grind)
    | exact superpose eq9912 eq4511
    | (have j0 := eq4511 X0
       have j1 := eq9912 X0 X0 X0
       grind)
    | exact resolve eq4511 eq9912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4511 eq9912
  have eq10259 : ∀ X0 : G, (M.op (k X0 (M.op X0 X0)) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq10151 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10151
  have eq10271 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq10139 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10139
  have eq10301 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  clear eq10259
  have eq10313 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  clear eq10271
  have eq17927 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) ∨ (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    grind
  clear eq432
  have eq17961 : ∀ X0 : G, (τ X0) = (k (M.op (τ X0) (τ X0)) (τ X0)) ∨ (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq17927 X0
       have i₂ := eq77 (τ X0) (τ X0)
       grind)
    | exact superpose eq77 eq17927
    | (have j0 := eq17927 X0
       grind)
    | exact resolve eq17927 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17927
  have eq22012 : ∀ X0 : G, (k X0 (τ (σ (k X0 X0)))) = (τ (M.op (σ X0) (σ (k X0 X0)))) ∨ (τ (M.op (σ X0) (σ (k X0 X0)))) = (k X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq4076 X0
       grind)
    | exact superpose eq4076 eq65
    | (have j1 := eq4076 X0
       grind)
    | exact resolve eq65 eq4076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq4076
  have eq22101 : ∀ X0 : G, (τ (M.op (σ X0) (σ (k X0 X0)))) = (k X0 (k X0 X0)) ∨ (τ (M.op (σ X0) (σ (k X0 X0)))) = (k X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq22012 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq22012
    | (have j0 := eq22012 X0
       grind)
    | exact resolve eq22012 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22012
  have eq22102 : ∀ X0 : G, (τ (M.op (σ X0) (σ (k X0 X0)))) = (k X0 (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq22101 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22101
  have eq22151 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (τ (M.op (σ X0) (σ (M.op X0 X0)))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq22102 x
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq22102
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq22102 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22177 : ∀ X0 : G, (k (τ X0) (k (τ X0) (τ X0))) = (τ (M.op (σ (τ X0)) (k X0 (σ (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq22102 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq22102
    | exact resolve eq22102 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22195 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ (k X0 X0)))
       have i₂ := eq22102 X0
       grind)
    | exact superpose eq22102 eq11
    | exact resolve eq11 eq22102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22270 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (τ (M.op (σ X0) (σ (M.op X0 X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq22151 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22151
  have eq22284 : ∀ X0 : G, (k (τ X0) (k (τ X0) (τ X0))) = (τ (M.op X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq22177 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22177
    | exact resolve eq22177 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22177
  have eq22297 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (τ (M.op (σ X0) (σ (M.op X0 X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  clear eq22270
  have eq22309 : ∀ X0 : G, (k (τ X0) (τ (k X0 X0))) = (τ (M.op X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq22284 X0
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq22284
    | exact resolve eq22284 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22284
  have eq22328 : ∀ X0 : G, (τ (k X0 (k X0 X0))) = (τ (M.op X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq22309 X0
       have i₂ := eq33 (k X0 X0) X0
       grind)
    | exact superpose eq33 eq22309
    | exact resolve eq22309 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq22309
  have eq22410 : ∀ X0 : G, (k X0 (k X0 X0)) = (σ (τ (M.op X0 (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 (k X0 X0))
       have i₂ := eq22328 X0
       grind)
    | exact superpose eq22328 eq11
    | exact resolve eq11 eq22328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22328
  have eq22544 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq22410 X0
       have i₂ := eq11 (M.op X0 (k X0 X0))
       grind)
    | exact superpose eq11 eq22410
    | exact resolve eq22410 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22410
  have eq22997 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 (k X0 X0))) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq77 (σ X0) (σ (k X0 X0))
       have i₂ := eq22195 X0
       grind)
    | exact superpose eq22195 eq77
    | exact resolve eq77 eq22195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22195
  have eq23000 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 (k X0 X0))) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq22997 X0
       have i₂ := eq22544 X0
       grind)
    | exact superpose eq22544 eq22997
    | exact resolve eq22997 eq22544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22997
  have eq23213 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (M.op X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq77 (σ (M.op X0 (k X0 X0))) (σ (k X0 X0))
       have i₂ := eq23000 X0
       grind)
    | exact superpose eq23000 eq77
    | exact resolve eq77 eq23000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23000
  have eq24059 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (k (τ X0) (τ X0))) (σ (k (τ X0) (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq20 X0 (k (τ X0) (τ X0))
       have i₂ := eq1051 (τ X0)
       grind)
    | exact superpose eq1051 eq20
    | (have j1 := eq1051 (τ X0)
       grind)
    | exact resolve eq20 eq1051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1051
  have eq24160 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (k (τ X0) (τ X0))) (σ (k (τ X0) (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq24059 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq24059
    | (have j0 := eq24059 X0
       grind)
    | exact resolve eq24059 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24059
  have eq24187 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ (τ X0)) = (M.op (σ (k (τ X0) (τ X0))) (σ (k (τ X0) (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq24160 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24160
    | (have j0 := eq24160 X0
       grind)
    | exact resolve eq24160 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24160
  have eq24213 : ∀ X0 : G, (σ (τ X0)) = (M.op (k (σ (τ X0)) X0) (k (σ (τ X0)) X0)) ∨ (k X0 X0) = (k (k X0 X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq24187 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq24187
    | (have j0 := eq24187 X0
       grind)
    | exact resolve eq24187 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24187
  have eq24238 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = (k (k X0 X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq24213 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24213
    | (have j0 := eq24213 X0
       grind)
    | exact resolve eq24213 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24213
  have eq24257 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq24238 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24238
    | (have j0 := eq24238 X0
       grind)
    | exact resolve eq24238 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24238
  have eq29998 : ∀ X0 : G, (M.op (τ X0) (M.op (τ X0) (τ X0))) = (τ (M.op (σ (τ X0)) (k X0 (σ (τ X0))))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq22297 (τ X0)
       have i₂ := eq419 (τ X0) X0
       grind)
    | exact superpose eq419 eq22297
    | (have j0 := eq22297 (τ X0)
       have j1 := eq419 (τ X0) X0
       grind)
    | exact resolve eq22297 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419 eq22297
  have eq30085 : ∀ X0 : G, (M.op (τ X0) (M.op (τ X0) (τ X0))) = (τ (M.op (σ (τ X0)) (k X0 (σ (τ X0))))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq29998 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29998
  have eq30097 : ∀ X0 : G, (M.op (τ X0) (M.op (τ X0) (τ X0))) = (τ (M.op X0 (k X0 X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq30085 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30085
    | (have j0 := eq30085 X0
       grind)
    | exact resolve eq30085 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30085
  have eq33567 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq77 (k X0 X0) (k X0 X0)
       have i₂ := eq24257 X0
       grind)
    | exact superpose eq24257 eq77
    | (have j1 := eq24257 X0
       grind)
    | exact resolve eq77 eq24257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24257
  have eq38300 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq10313 X0
       have i₂ := eq33567 X0
       grind)
    | exact superpose eq33567 eq10313
    | (have j0 := eq10313 X0
       have j1 := eq33567 X0
       grind)
    | exact resolve eq10313 eq33567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10313 eq33567
  have eq38371 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (M.op X0 X0)) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq38300 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38300
  have eq38577 : ∀ X0 : G, (k (M.op X0 X0) X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (M.op X0 X0)) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq9647 X0 X0 X0
       have i₂ := eq38371 X0
       grind)
    | exact superpose eq38371 eq9647
    | (have j0 := eq9647 X0 X0 X0
       have j1 := eq38371 X0
       grind)
    | exact resolve eq9647 eq38371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9647 eq38371
  have eq38649 : ∀ X0 : G, (k (M.op X0 X0) X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (M.op X0 X0)) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq38577 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38577
  have eq38955 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op X0 (k X0 X0))) (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq77 (τ X0) (M.op (τ X0) (τ X0))
       have i₂ := eq30097 X0
       grind)
    | exact superpose eq30097 eq77
    | (have j1 := eq30097 X0
       grind)
    | exact resolve eq77 eq30097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30097
  have eq40339 : ∀ X0 : G, (M.op (τ (M.op (σ X0) (k (σ X0) (σ X0)))) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq38955 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq38955
    | exact resolve eq38955 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38955
  have eq40389 : ∀ X0 : G, (M.op (τ (M.op (σ X0) (σ (k X0 X0)))) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq40339 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq40339
    | (have j0 := eq40339 X0
       grind)
    | exact resolve eq40339 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40339
  have eq40412 : ∀ X0 : G, (M.op (k X0 (k X0 X0)) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq40389 X0
       have i₂ := eq22102 X0
       grind)
    | exact superpose eq22102 eq40389
    | (have j0 := eq40389 X0
       grind)
    | exact resolve eq40389 eq22102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22102 eq40389
  have eq40427 : ∀ X0 : G, (M.op (M.op X0 (k X0 X0)) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq40412 X0
       have i₂ := eq22544 X0
       grind)
    | exact superpose eq22544 eq40412
    | (have j0 := eq40412 X0
       grind)
    | exact resolve eq40412 eq22544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40412
  have eq58421 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (σ (M.op X0 X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq17961 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17961
    | exact resolve eq17961 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17961
  have eq58503 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (σ (M.op X0 X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq58421 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq58421
    | (have j0 := eq58421 X0
       grind)
    | exact resolve eq58421 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58421
  have eq58657 : ∀ X0 : G, (k X0 X0) = X0 ∨ (σ (M.op X0 X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (M.op X0 X0)) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq58503 X0
       have i₂ := eq38649 X0
       grind)
    | exact superpose eq38649 eq58503
    | (have j1 := eq38649 X0
       grind)
    | exact resolve eq58503 eq38649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38649 eq58503
  have eq58755 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (M.op X0 X0)) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq58657 X0
       have j1 := eq1074 X0
       grind)
    | (have r₁ := eq58657 X0
       have r₂ := eq1074 X0
       grind)
    | exact resolve eq58657 eq1074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58657
  have eq132859 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (M.op X0 X0)) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq58755 X0
       grind)
    | exact superpose eq58755 eq10
    | (have j1 := eq58755 X0
       grind)
    | exact resolve eq10 eq58755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58755
  have eq133029 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq132859 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq132859
    | (have j0 := eq132859 X0
       grind)
    | exact resolve eq132859 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132859
  have eq133726 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq10301 X0
       have i₂ := eq133029 X0
       grind)
    | exact superpose eq133029 eq10301
    | (have j0 := eq10301 X0
       have j1 := eq133029 X0
       grind)
    | exact resolve eq10301 eq133029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10301
  have eq133963 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq133726 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133726
  have eq134645 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq133963
  have eq134778 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq134645 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134645
  have eq134878 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq134778 X0
       have i₂ := eq22544 X0
       grind)
    | exact superpose eq22544 eq134778
    | (have j0 := eq134778 X0
       grind)
    | exact resolve eq134778 eq22544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22544 eq134778
  have eq134993 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq40427 X0
       have i₂ := eq134878 X0
       grind)
    | exact superpose eq134878 eq40427
    | (have j0 := eq40427 X0
       have j1 := eq134878 X0
       grind)
    | exact resolve eq40427 eq134878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40427 eq134878
  have eq135120 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq134993 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134993
  have eq135349 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq133029 X0
       have i₂ := eq135120 X0
       grind)
    | exact superpose eq135120 eq133029
    | (have j0 := eq133029 X0
       have j1 := eq135120 X0
       grind)
    | exact resolve eq133029 eq135120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133029 eq135120
  have eq135569 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq135349 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135349
  have eq135680 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq135569 X0
       have j1 := eq1074 X0
       grind)
    | (have r₁ := eq135569 X0
       have r₂ := eq1074 X0
       grind)
    | exact resolve eq135569 eq1074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074 eq135569
  have eq136017 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq135680 (σ X0)
       grind)
    | exact superpose eq135680 eq15
    | (have j1 := eq135680 (σ X0)
       grind)
    | exact resolve eq15 eq135680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135680
  have eq136352 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  clear eq136017
  have eq136450 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq136352 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq136352
    | (have j0 := eq136352 X0
       grind)
    | exact resolve eq136352 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136352
  have eq136451 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq136450 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136450
  have eq136510 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq136451 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq136451
    | exact resolve eq136451 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136757 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq77 (σ X0) (σ X0)
       have i₂ := eq136451 X0
       grind)
    | exact superpose eq136451 eq77
    | exact resolve eq77 eq136451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136956 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq136510 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq136510
    | exact resolve eq136510 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136510
  have eq137072 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq136956 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq136956
    | exact resolve eq136956 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136956
  have eq137369 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq23213 X0
       have i₂ := eq137072 X0
       grind)
    | exact superpose eq137072 eq23213
    | exact resolve eq23213 eq137072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23213
  have eq138007 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq136757 X0
       have i₂ := eq137072 X0
       grind)
    | exact superpose eq137072 eq136757
    | exact resolve eq136757 eq137072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136757
  have eq2418900 : ∀ X0 X1 : G, (σ X1) = (M.op (k X0 (σ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1034 (τ X0) X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq1034
    | (have j0 := eq1034 (τ X0) X1
       grind)
    | exact resolve eq1034 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1034
  have eq2419828 : ∀ X0 X1 : G, (σ X1) = (M.op (k X0 (σ X1)) X0) ∨ (σ (τ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2418900 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2418900
    | (have j0 := eq2418900 X0 X1
       grind)
    | exact resolve eq2418900 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2418900
  have eq2420336 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op (k X0 (σ X1)) X0) ∨ (σ X1) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2419828 X0 X1
       have i₂ := eq136451 X1
       grind)
    | exact superpose eq136451 eq2419828
    | (have j0 := eq2419828 X0 X1
       grind)
    | exact resolve eq2419828 eq136451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2419828
  have eq2420797 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (k X0 (σ X1)) X0) ∨ (σ X1) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2420336 X0 X1
       have i₂ := eq137072 X1
       grind)
    | exact superpose eq137072 eq2420336
    | (have j0 := eq2420336 X0 X1
       grind)
    | exact resolve eq2420336 eq137072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2420336
  have eq2421242 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = X0 ∨ (σ X1) = (M.op (k X0 (σ X1)) X0) ∨ (σ X1) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2420797 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2420797
    | (have j0 := eq2420797 X0 X1
       grind)
    | exact resolve eq2420797 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2420797
  have eq2421595 : ∀ X0 X1 : G, (σ X1) = (σ (k (τ X0) (τ X0))) ∨ (σ (M.op X1 X1)) = X0 ∨ (σ X1) = (M.op (k X0 (σ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2421242 X0 X1
       have i₂ := eq136451 (τ X0)
       grind)
    | exact superpose eq136451 eq2421242
    | (have j0 := eq2421242 X0 X1
       grind)
    | exact resolve eq2421242 eq136451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2421242
  have eq2421902 : ∀ X0 X1 : G, (σ X1) = (k (σ (τ X0)) X0) ∨ (σ (M.op X1 X1)) = X0 ∨ (σ X1) = (M.op (k X0 (σ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2421595 X0 X1
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq2421595
    | (have j0 := eq2421595 X0 X1
       grind)
    | exact resolve eq2421595 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2421595
  have eq2422159 : ∀ X0 X1 : G, (σ X1) = (k X0 X0) ∨ (σ (M.op X1 X1)) = X0 ∨ (σ X1) = (M.op (k X0 (σ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2421902 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2421902
    | (have j0 := eq2421902 X0 X1
       grind)
    | exact resolve eq2421902 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2421902
  have eq2422405 : ∀ X0 X1 : G, (σ X1) = (M.op (k X0 (σ X1)) X0) ∨ (σ (M.op X1 X1)) = X0 ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2422159 X0 X1
       have i₂ := eq137072 X0
       grind)
    | exact superpose eq137072 eq2422159
    | (have j0 := eq2422159 X0 X1
       grind)
    | exact resolve eq2422159 eq137072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2422159
  have eq2423855 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = X1 ∨ (M.op X1 X1) = (σ X0) := by
    intro X0 X1
    first
    | (have i₁ := eq77 (k X1 (σ X0)) X1
       have i₂ := eq2422405 X1 X0
       grind)
    | exact superpose eq2422405 eq77
    | (have j1 := eq2422405 X1 X0
       grind)
    | exact resolve eq77 eq2422405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2422405
  have eq2429384 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq2423855 X0 (σ X1)
       grind)
    | exact superpose eq2423855 eq15
    | (have j1 := eq2423855 X0 (σ X1)
       grind)
    | exact resolve eq15 eq2423855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2423855
  have eq2429800 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2429384 X0 X1
       have i₂ := eq136451 X1
       grind)
    | exact superpose eq136451 eq2429384
    | (have j0 := eq2429384 X0 X1
       grind)
    | exact resolve eq2429384 eq136451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136451 eq2429384
  have eq2430220 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2429800 X0 X1
       have i₂ := eq137072 X1
       grind)
    | exact superpose eq137072 eq2429800
    | (have j0 := eq2429800 X0 X1
       grind)
    | exact resolve eq2429800 eq137072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137072 eq2429800
  have eq2446216 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2430220 x y
       grind)
    | exact superpose eq2430220 eq16
    | (have j1 := eq2430220 x y
       grind)
    | exact resolve eq16 eq2430220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2430220
  have eq2453133 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2446216
       have i₂ := eq6853 x y
       grind)
    | exact superpose eq6853 eq2446216
    | (have j1 := eq6853 x y
       grind)
    | (have r₁ := eq2446216
       have r₂ := eq6853 x y
       grind)
    | exact resolve eq2446216 eq6853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6853 eq2446216
  have eq2453134 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq2453133
  have eq2457092 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq2453134
       grind)
    | exact superpose eq2453134 eq10
    | exact resolve eq10 eq2453134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2453134
  have eq2457780 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2457092
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2457092
    | exact resolve eq2457092 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2457092
  have eq2457781 : (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq2457780
  have eq2458169 : (M.op y y) = (τ (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq2457781
       grind)
    | exact superpose eq2457781 eq10
    | exact resolve eq10 eq2457781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2457781
  have eq2458857 : x = (M.op y y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2458169
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2458169
    | exact resolve eq2458169 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2458169
  have eq2458858 : y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq2458857
  have eq2459347 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq137369 x
       have i₂ := eq2458858
       grind)
    | exact superpose eq2458858 eq137369
    | exact resolve eq137369 eq2458858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137369 eq2458858
  have eq2459874 : x = (M.op y y) := by
    first
    | (have r₁ := eq2459347
       have r₂ := eq16
       grind)
    | exact resolve eq2459347 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2459347
  have eq2460291 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq138007 y
       have i₂ := eq2459874
       grind)
    | exact superpose eq2459874 eq138007
    | exact resolve eq138007 eq2459874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138007
  have eq2460655 : y = (M.op x y) := by
    first
    | (have i₁ := eq77 y y
       have i₂ := eq2459874
       grind)
    | exact superpose eq2459874 eq77
    | exact resolve eq77 eq2459874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq2459874
  have eq2461276 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2460291
       grind)
    | exact superpose eq2460291 eq16
    | exact resolve eq16 eq2460291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2460291
  have eq2461452 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq2461276
       have i₂ := eq2460655
       grind)
    | exact superpose eq2460655 eq2461276
    | exact resolve eq2461276 eq2460655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2460655 eq2461276
  have eq2461453 : False := by grind
  exact eq2461453

/-- `Equation2477`: `x = (x ◇ ((y ◇ z) ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(X,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_pxy_pyy_pyx_Equation2477 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2477 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2477.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X0)) X1) = X0 := by
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op X0 (M.op (M.op X2 X3) X0))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op X0 (M.op (M.op X2 X3) X0)) X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op (M.op X1 x) X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq54 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq54
    | (have j0 := eq54 y x
       grind)
    | exact resolve eq54 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq27 eq54
    | (have j0 := eq54 (σ y) (σ x)
       grind)
    | exact resolve eq54 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) X0)) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X1 (M.op X0 (M.op (M.op X1 X2) X0))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op X0 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X0 X2) X2
       have i₂ := eq54 X2 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) X0)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq93 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq94 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq95 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq98 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op (M.op X0 (M.op (M.op X1 X2) X0)) (M.op X0 (M.op (M.op X1 X2) X0))) = X1 ∨ (M.op X1 X1) = (k (M.op X0 (M.op (M.op X1 X2) X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 (M.op (M.op X1 X2) X0)) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op X0 (M.op (M.op X1 X2) X0)) X1
       grind)
    | (have r₁ := eq12 (M.op X0 (M.op (M.op X0 X2) X0)) X0
       have r₂ := eq14 X0 X0 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq93
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq93
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq93 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq16
    | exact resolve eq16 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq104
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq104
    | exact resolve eq104 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq110
    | exact resolve eq110 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq112 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq94
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq94 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq94
       grind)
    | exact superpose eq94 eq16
    | exact resolve eq16 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq112
  have eq119 : (k (σ y) (σ (M.op x y))) = (σ (M.op (M.op x y) y)) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq11 y sF0
       grind)
    | exact superpose eq11 eq95
    | (have j1 := eq11 y (M.op x y)
       grind)
    | exact resolve eq95 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq55 eq119
    | exact resolve eq119 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq126 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq125
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq125
    | exact resolve eq125 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq180 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq117
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq117
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq117 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq180
  have eq400 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq436 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq63 eq54
    | exact resolve eq54 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq587 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq73 X0 X1
       grind)
    | exact superpose eq73 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq73 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq73 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq73 X1 X1
       grind)
    | exact resolve eq12 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq588 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (σ X0) (σ X1)
       have i₂ := eq73 X0 X1
       grind)
    | exact superpose eq73 eq54
    | (have j1 := eq73 X0 X1
       grind)
    | exact resolve eq54 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq591 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq73 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq592 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq591 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq595 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq587 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq587
    | (have j0 := eq587 X0 X1
       grind)
    | exact resolve eq587 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq733 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X1) X0)) (M.op X0 (M.op (M.op X0 X1) X0))) = X0 ∨ (M.op X0 X0) = (k (M.op X0 (M.op (M.op X0 X1) X0)) X0) := by
    intro X0 X1
    first
    | (have j0 := eq98 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq986 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X1)) = (M.op X1 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X1 (M.op X0 X2) X2
       have i₂ := eq54 X2 X0
       grind)
    | exact superpose eq54 eq57
    | exact resolve eq57 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1012 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) (M.op (M.op X3 X4) (M.op X1 X2)))) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op X1 X2) X0 X3 X4
       have i₂ := eq57 X0 X1 X2
       grind)
    | exact superpose eq57 eq53
    | exact resolve eq53 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1040 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1012 X0 X1 X2 X3 x
       have i₂ := eq57 (M.op X1 X2) X3 x
       grind)
    | exact superpose eq57 eq1012
    | exact resolve eq1012 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012
  have eq1075 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq436 eq59
    | exact resolve eq59 eq436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436
  have eq1268 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1075 (M.op X1 sF4) X1
       have i₂ := eq54 sF4 X1
       grind)
    | exact superpose eq54 eq1075
    | exact resolve eq1075 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1451 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq986 (M.op X0 X1) X1 X2
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq986
    | exact resolve eq986 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1476 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq986 (M.op X1 X2) X0 X3
       have i₂ := eq57 X0 X1 X2
       grind)
    | exact superpose eq57 eq986
    | exact resolve eq986 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1947 : ∀ X0 X1 : G, (M.op x y) = (M.op x (M.op (M.op y X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq55 eq1040
    | exact resolve eq1040 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1951 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ y) X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq56 eq1040
    | exact resolve eq1040 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4411 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq592 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq592
    | (have j0 := eq592 (τ X0)
       grind)
    | exact resolve eq592 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq592
  have eq4419 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4411 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4411
    | (have j0 := eq4411 X0
       grind)
    | exact resolve eq4411 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4411
  have eq4425 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4419 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4419
    | (have j0 := eq4419 X0
       grind)
    | exact resolve eq4419 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4419
  have eq5239 : (σ y) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq588 y y
       have i₂ := eq94
       grind)
    | exact superpose eq94 eq588
    | (have j0 := eq588 y y
       grind)
    | exact resolve eq588 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq5240 : (σ (M.op x y)) = (M.op (k (σ y) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq95 eq588
    | (have j0 := eq588 y (M.op x y)
       grind)
    | exact resolve eq588 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq5303 : (σ y) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq5239
  have eq5319 : (σ (M.op x y)) = (M.op (k (σ y) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5240
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq5240
    | exact resolve eq5240 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5240
  have eq5320 : (σ y) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5303
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq5303
    | exact resolve eq5303 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5303
  have eq5356 : (σ (M.op x y)) = (M.op (k (σ y) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq21 eq5319
    | exact resolve eq5319 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5319
  have eq5357 : (σ y) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5320
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq5320
    | exact resolve eq5320 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5320
  have eq5389 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (k (σ y) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq21 eq5356
    | exact resolve eq5356 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5356
  have eq5420 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (k (σ y) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5389
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq5389
    | exact resolve eq5389 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5389
  have eq5448 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (k (σ y) (σ (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq5420
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq5420
    | exact resolve eq5420 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5420
  have eq5476 : (σ (M.op x y)) = (M.op (k (σ y) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq21 eq5448
    | exact resolve eq5448 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5448
  have eq5836 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (k (M.op X0 (M.op (M.op X0 X1) X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq733 X1 x
       have i₂ := eq57 X1 X1 x
       grind)
    | exact superpose eq57 eq733
    | (have j0 := eq733 X0 X1
       grind)
    | exact resolve eq733 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq5837 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq5836 X0 x
       have i₂ := eq57 X0 X0 x
       grind)
    | exact superpose eq57 eq5836
    | (have j0 := eq5836 X0 x
       grind)
    | exact resolve eq5836 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5836
  have eq5877 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq5882 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq54 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq5837 X0
       grind)
    | exact superpose eq5837 eq54
    | (have j1 := eq5837 X0
       grind)
    | exact resolve eq54 eq5837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5837
  have eq5902 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5877 X0
       have i₂ := eq54 X0 X0
       grind)
    | exact superpose eq54 eq5877
    | (have j0 := eq5877 X0
       grind)
    | exact resolve eq5877 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5877
  have eq5913 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X0) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq400 X1 x
       have i₂ := eq57 (M.op X1 x) X1 x
       grind)
    | exact superpose eq57 eq400
    | exact resolve eq400 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq400
  have eq5918 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 (M.op X0 X1)))) = (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq5913 (M.op X0 x) (M.op X0 (M.op X0 x))
       have i₂ := eq59 X0 (M.op X0 x) x
       grind)
    | exact superpose eq59 eq5913
    | exact resolve eq5913 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq5913
  have eq6028 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq5918 X0 X1
       have i₂ := eq1476 (M.op X0 X1) X0 X1 (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq1476 eq5918
    | exact resolve eq5918 eq1476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1476 eq5918
  have eq12922 : (M.op y y) = (τ (k (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq118
       grind)
    | exact superpose eq118 eq16
    | exact resolve eq16 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12972 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq117 eq12922
    | exact resolve eq12922 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12922
  have eq20583 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq111 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq20584 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq20583
    | exact resolve eq20583 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20583
  have eq20595 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq20584
       have r₂ := eq28
       grind)
    | exact resolve eq20584 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20584
  have eq20616 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (M.op (M.op (σ y) X0) X1)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq20595 eq1040
    | exact resolve eq1040 eq20595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20595
  have eq20628 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1951 eq20616
    | exact resolve eq20616 eq1951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20616
  have eq20650 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20628 eq54
    | exact resolve eq54 eq20628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20628
  have eq25085 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq126 eq5476
    | exact resolve eq5476 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5476
  have eq25116 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq27 eq25085
    | exact resolve eq25085 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25085
  have eq25117 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq25116
       have r₂ := eq28
       grind)
    | exact resolve eq25116 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25116
  have eq25139 : (k (σ y) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq25117
  have eq25449 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq25139 eq126
    | exact resolve eq126 eq25139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq25139
  have eq25466 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by grind
  clear eq25449
  have eq25483 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq25466 eq54
    | exact resolve eq54 eq25466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25466
  have eq60324 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20650 eq5882
    | exact resolve eq5882 eq20650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20650
  have eq60423 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq60324
    | exact resolve eq60324 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60324
  have eq60424 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq60423
  have eq81046 : (τ (σ y)) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq60424 eq109
    | exact resolve eq109 eq60424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq60424
  have eq81076 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq81046
    | exact resolve eq81046 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81046
  have eq81099 : y = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq81076
       grind)
    | exact superpose eq81076 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq81076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81076
  have eq81100 : y = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq81099
  have eq81106 : x = (M.op y y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq81100
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq81100
    | exact resolve eq81100 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81100
  have eq81177 : ∀ X0 X1 : G, y = (M.op x (M.op (M.op y X0) X1)) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1040 y y X0 X1
       have i₂ := eq81106
       grind)
    | exact superpose eq81106 eq1040
    | exact resolve eq1040 eq81106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81106
  have eq81206 : y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq81177 x x
       have i₂ := eq1947 x x
       grind)
    | exact superpose eq1947 eq81177
    | exact resolve eq81177 eq1947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81177
  have eq81207 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq81206
  have eq81244 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54 x y
       have i₂ := eq81207
       grind)
    | exact superpose eq81207 eq54
    | exact resolve eq54 eq81207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81207
  have eq81311 : y = (k y x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5882 x
       have i₂ := eq81244
       grind)
    | exact superpose eq81244 eq5882
    | exact resolve eq5882 eq81244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5882
  have eq81316 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq81244
  have eq81355 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq81316
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq81316
    | exact resolve eq81316 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81316
  have eq81358 : y = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq81311
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq81311
    | exact resolve eq81311 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq81311
  have eq81359 : y = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq81358
  have eq83297 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq81355
       grind)
    | exact superpose eq81355 eq45
    | exact resolve eq45 eq81355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq81355
  have eq83341 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq83297
    | exact resolve eq83297 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83297
  have eq83934 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq588 y x
       have i₂ := eq81359
       grind)
    | exact superpose eq81359 eq588
    | (have j0 := eq588 y x
       grind)
    | exact resolve eq588 eq81359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588 eq81359
  have eq83936 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq83934
  have eq83940 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq83936
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq83936
    | exact resolve eq83936 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83936
  have eq83957 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq83940
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq83940
    | exact resolve eq83940 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83940
  have eq83961 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq83957
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq83957
    | exact resolve eq83957 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83957
  have eq83965 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq83961
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq83961
    | exact resolve eq83961 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83961
  have eq103974 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (M.op (M.op (σ y) X0) X1)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq83965 eq1040
    | exact resolve eq1040 eq83965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83965
  have eq104007 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1951 eq103974
    | exact resolve eq103974 eq1951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1951 eq103974
  have eq104008 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq104007
  have eq104048 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq104008 eq54
    | exact resolve eq54 eq104008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq104008
  have eq104423 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq104048
  have eq104476 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq104423
    | exact resolve eq104423 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104423
  have eq105881 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq104476 eq83341
    | exact resolve eq83341 eq104476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83341 eq104476
  have eq105891 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq105881
  have eq105910 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq105891
       have r₂ := eq28
       grind)
    | exact resolve eq105891 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105891
  have eq105920 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq105910 eq56
    | exact resolve eq56 eq105910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq105930 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) X1)) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq105910 eq1075
    | exact resolve eq1075 eq105910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075
  have eq105972 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1268 eq105930
    | (have j0 := eq105930 X0 (σ y)
       grind)
    | exact resolve eq105930 eq1268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105930
  have eq106287 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq105920 eq182
    | exact resolve eq182 eq105920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq106329 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq105920 eq1451
    | exact resolve eq1451 eq105920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1451
  have eq106337 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (M.op (σ y) (σ x)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq105920 eq6028
    | exact resolve eq6028 eq105920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6028 eq105920
  have eq106344 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (M.op (σ y) (σ x)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq106337
    | exact resolve eq106337 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106337
  have eq106347 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1268 eq106329
    | (have j0 := eq106329 (σ y)
       grind)
    | exact resolve eq106329 eq1268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106329
  have eq106359 : x = (k y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq106287
    | exact resolve eq106287 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106287
  have eq107146 : (k (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq5357 eq105972
    | exact resolve eq105972 eq5357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5357 eq105972
  have eq112448 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq106359
       have i₂ := eq12972
       grind)
    | exact superpose eq12972 eq106359
    | exact resolve eq106359 eq12972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12972
  have eq117236 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (M.op (σ y) X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq106344
       have i₂ := eq986 sF3 sF2 x
       grind)
    | (have i₁ := eq106344
       have i₂ := eq986 sF3 sF2 sF2
       grind)
    | exact superpose eq986 eq106344
    | exact resolve eq106344 eq986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986 eq106344
  have eq176173 : (k y y) = (τ (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq107146 eq117
    | exact resolve eq117 eq107146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176193 : (σ y) ≠ (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq107146 eq4425
    | (have j0 := eq4425 (σ y)
       grind)
    | exact resolve eq4425 eq107146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107146
  have eq176213 : (σ y) ≠ (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq176193
  have eq176229 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq106347 eq176213
    | exact resolve eq176213 eq106347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176213
  have eq176238 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq176229
  have eq229132 : x ≠ y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq112448
  have eq230731 : (τ (σ x)) = (k y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq106347 eq176173
    | exact resolve eq176173 eq106347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106347 eq176173
  have eq231102 : (τ (σ x)) = (k y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq230731
  have eq231114 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (k y y) := by
    first
    | exact superpose eq29 eq231102
    | exact resolve eq231102 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231102
  have eq231191 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (k y y) := by
    first
    | exact superpose eq231114 eq5902
    | exact resolve eq5902 eq231114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231114
  have eq231218 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (k y y) := by grind
  clear eq231191
  have eq231283 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) ∨ x = (k y y) := by
    first
    | exact superpose eq231218 eq117
    | exact resolve eq117 eq231218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231218
  have eq231379 : y = (k y y) ∨ y = (M.op x y) ∨ x = (k y y) := by
    first
    | exact superpose eq30 eq231283
    | exact resolve eq231283 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231283
  have eq232412 : y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq231379
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq231379
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq231379 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231379
  have eq232496 : y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq232412
  have eq234168 : y = (k y y) ∨ y = (k y y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq5902 y
       have i₂ := eq232496
       grind)
    | exact superpose eq232496 eq5902
    | exact resolve eq5902 eq232496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234196 : x ≠ y ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq232496
  have eq234197 : y = (k y y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq234168
  have eq236807 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq106359
       have i₂ := eq234197
       grind)
    | exact superpose eq234197 eq106359
    | exact resolve eq106359 eq234197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106359 eq234197
  have eq236875 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq236807
  have eq236913 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq236875
       have r₂ := eq229132
       grind)
    | exact resolve eq236875 eq229132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229132 eq236875
  have eq237040 : ∀ X0 X1 : G, y = (M.op x (M.op (M.op y X0) X1)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq1040 y y X0 X1
       have i₂ := eq236913
       grind)
    | exact superpose eq236913 eq1040
    | exact resolve eq1040 eq236913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236913
  have eq237081 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq237040 x x
       have i₂ := eq1947 x x
       grind)
    | exact superpose eq1947 eq237040
    | exact resolve eq237040 eq1947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237040
  have eq237082 : (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq237081
  have eq237245 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq237082 eq27
    | exact resolve eq27 eq237082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237246 : y = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq237082 eq30
    | exact resolve eq30 eq237082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237261 : (τ (k (σ x) (σ x))) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq237082 eq117
    | exact resolve eq117 eq237082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237479 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (M.op (σ x) X0))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq237082 eq117236
    | exact resolve eq117236 eq237082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117236
  have eq237537 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq237082 eq176238
    | (have r₁ := eq176238
       have r₂ := eq237082
       grind)
    | exact resolve eq176238 eq237082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176238 eq237082
  have eq237685 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq237537
  have eq237686 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq237685
  have eq237745 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (M.op (σ x) X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq237479 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237479
  have eq237840 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1268 eq237745
    | (have j0 := eq237745 (σ y)
       grind)
    | exact resolve eq237745 eq1268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1268 eq237745
  have eq237936 : (k x x) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq50 eq237261
    | exact resolve eq237261 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237261
  have eq237947 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq237246
    | exact resolve eq237246 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237246
  have eq238133 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq237947 eq21
    | exact resolve eq21 eq237947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238136 : x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq237947 eq55
    | exact resolve eq55 eq237947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237947
  have eq238505 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq238133
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq238133
    | exact resolve eq238133 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238133
  have eq239633 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq237686 eq237245
    | exact resolve eq237245 eq237686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237245 eq237686
  have eq239685 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq239633
  have eq240507 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq118
       have i₂ := eq238136
       grind)
    | exact superpose eq238136 eq118
    | exact resolve eq118 eq238136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq238136
  have eq240576 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by grind
  clear eq240507
  have eq240598 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq240576
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq240576
    | exact resolve eq240576 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240576
  have eq243199 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq238505 eq240598
    | exact resolve eq240598 eq238505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238505
  have eq243207 : (τ (σ x)) = (k y y) ∨ x = y := by
    first
    | exact superpose eq240598 eq117
    | exact resolve eq117 eq240598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq240598
  have eq243267 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq243199
  have eq243278 : x = (k y y) ∨ x = y := by
    first
    | exact superpose eq29 eq243207
    | exact resolve eq243207 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243207
  have eq256160 : (σ y) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq105910 eq237840
    | exact resolve eq237840 eq105910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105910 eq237840
  have eq256200 : (σ y) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq256160
  have eq256206 : (σ y) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq256200
    | exact resolve eq256200 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256200
  have eq256935 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq239685 eq256206
    | exact resolve eq256206 eq239685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239685 eq256206
  have eq256984 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq256935
  have eq257986 : (τ (σ y)) = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq256984 eq50
    | exact resolve eq50 eq256984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq256984
  have eq258074 : y = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq257986
    | exact resolve eq257986 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq257986
  have eq263812 : y ≠ (k x x) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4425 y
       have i₂ := eq237936
       grind)
    | exact superpose eq237936 eq4425
    | (have j0 := eq4425 y
       grind)
    | exact resolve eq4425 eq237936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4425 eq237936
  have eq263874 : y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq263812
       have r₂ := eq258074
       grind)
    | exact resolve eq263812 eq258074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258074 eq263812
  have eq264036 : (k y y) = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq263874
  have eq303506 : x = (M.op y y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq264036
       have i₂ := eq243278
       grind)
    | exact superpose eq243278 eq264036
    | exact resolve eq264036 eq243278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243278 eq264036
  have eq303648 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq303506
       have r₂ := eq234196
       grind)
    | exact resolve eq303506 eq234196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234196 eq303506
  have eq304160 : ∀ X0 X1 : G, y = (M.op x (M.op (M.op y X0) X1)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1040 y y X0 X1
       have i₂ := eq303648
       grind)
    | exact superpose eq303648 eq1040
    | exact resolve eq1040 eq303648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040 eq303648
  have eq304207 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq304160 x x
       have i₂ := eq1947 x x
       grind)
    | exact superpose eq1947 eq304160
    | exact resolve eq304160 eq1947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1947 eq304160
  have eq304208 : y = (M.op x y) := by grind
  clear eq304207
  have eq304226 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq304208 eq21
    | exact resolve eq21 eq304208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq304229 : x = (M.op y y) := by
    first
    | exact superpose eq304208 eq55
    | exact resolve eq55 eq304208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq304630 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq304226
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq304226
    | exact resolve eq304226 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304226
  have eq305945 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq304630 eq27
    | exact resolve eq27 eq304630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq306675 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq305945 eq25483
    | exact resolve eq25483 eq305945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25483
  have eq306720 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq304630 eq306675
    | exact resolve eq306675 eq304630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306675
  have eq306725 : (M.op x y) = (M.op y (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq306720
       have r₂ := eq28
       grind)
    | exact resolve eq306720 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306720
  have eq306727 : y = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq304208 eq306725
    | exact resolve eq306725 eq304208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306725
  have eq306729 : x = y ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq306727
       have i₂ := eq304229
       grind)
    | exact superpose eq304229 eq306727
    | exact resolve eq306727 eq304229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306727
  have eq306731 : x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq306729
       have i₂ := eq304229
       grind)
    | exact superpose eq304229 eq306729
    | exact resolve eq306729 eq304229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306729
  have eq306733 : x = y ∨ x = y ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq304208 eq306731
    | exact resolve eq306731 eq304208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306731
  have eq306734 : x = y ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by grind
  clear eq306733
  have eq306737 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq304630 eq306734
    | exact resolve eq306734 eq304630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306734
  have eq308780 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq306737 eq5902
    | exact resolve eq5902 eq306737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306737
  have eq308810 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq308780
  have eq308866 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq308810 eq243267
    | exact resolve eq243267 eq308810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243267 eq308810
  have eq308915 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq308866
  have eq308956 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq308915 eq29
    | exact resolve eq29 eq308915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq308915
  have eq309537 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq308956
    | exact resolve eq308956 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq308956
  have eq309632 : x = y ∨ x = y := by
    first
    | exact superpose eq304208 eq309537
    | exact resolve eq309537 eq304208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304208 eq309537
  have eq309633 : x = y := by grind
  clear eq309632
  have eq309689 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq309633
       grind)
    | exact superpose eq309633 eq25
    | exact resolve eq25 eq309633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq310004 : x = (M.op x x) := by
    first
    | (have i₁ := eq304229
       have i₂ := eq309633
       grind)
    | exact superpose eq309633 eq304229
    | exact resolve eq304229 eq309633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304229 eq309633
  have eq310302 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq304630 eq309689
    | exact resolve eq309689 eq304630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304630 eq309689
  have eq310531 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq310302
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq310302
    | exact resolve eq310302 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310302
  have eq314007 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq310531 eq305945
    | exact resolve eq305945 eq310531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305945
  have eq314354 : x = (k x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq5902 x
       have i₂ := eq310004
       grind)
    | exact superpose eq310004 eq5902
    | exact resolve eq5902 eq310004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5902 eq310004
  have eq314385 : x = (k x x) := by grind
  clear eq314354
  have eq329871 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq595 x x
       have i₂ := eq314385
       grind)
    | exact superpose eq314385 eq595
    | (have j0 := eq595 x x
       grind)
    | exact resolve eq595 eq314385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595 eq314385
  have eq329888 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq329871
  have eq329889 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq329888
  have eq329918 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq329889
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq329889
    | exact resolve eq329889 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq329889
  have eq329974 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq310531 eq329918
    | exact resolve eq329918 eq310531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310531 eq329918
  have eq330029 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq314007 eq329974
    | exact resolve eq329974 eq314007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314007 eq329974
  have eq330082 : False := by grind
  exact eq330082

/-- `Equation2503`: `x = (y ◇ ((x ◇ y) ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_pyx_pyx_pxy_pyx_Equation2503 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2503 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2503.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
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
  have eq89 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq336 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq89 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq89 X0 X1
       grind)
    | exact superpose eq89 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq89 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq89 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq89 X0 X1
       grind)
    | exact resolve eq13 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq337 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq89 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq89 X0 X1
       grind)
    | exact superpose eq89 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq89 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq89 X0 X1
       grind)
    | exact resolve eq12 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq350 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq336 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq355 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq337 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq337 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq337 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq356 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq350 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq350 X1 X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq350 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq350 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq364 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq355 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq355
    | (have j0 := eq355 X0 X1
       grind)
    | exact resolve eq355 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq365 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq364 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq366 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq356 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq356
    | (have j0 := eq356 X0 X1
       grind)
    | exact resolve eq356 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq367 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq366 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq370 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq367 X0 X1
       have j1 := eq365 X0 X1
       grind)
    | (have r₁ := eq367 X0 X1
       have r₂ := eq365 X0 X1
       grind)
    | exact resolve eq367 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365 eq367
  have eq371 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq370 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq370
    | exact resolve eq370 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq382 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq370 x y
       grind)
    | exact superpose eq370 eq16
    | exact resolve eq16 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq449 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq371 X0 (τ X1)
       grind)
    | exact superpose eq371 eq17
    | exact resolve eq17 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq371
  have eq480 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq449 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq449
    | exact resolve eq449 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449
  have eq495 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq480 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq480
    | exact resolve eq480 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq534 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq382
       have i₂ := eq495 x y
       grind)
    | exact superpose eq495 eq382
    | exact resolve eq382 eq495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382 eq495
  have eq535 : False := by grind
  exact eq535

/-- `Equation2503`: `x = (y ◇ ((x ◇ y) ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pyy_pyx_Equation2503 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2503 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2503.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24
    | exact resolve eq24 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq53 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq53 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq53 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq54 (σ X0)
       grind)
    | exact superpose eq54 eq15
    | exact resolve eq15 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq54 (τ X0)
       grind)
    | exact superpose eq54 eq18
    | exact resolve eq18 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq62 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq59 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq59
    | exact resolve eq59 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq56 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq62 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq62
    | exact resolve eq62 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq62
  have eq78 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq13
    | exact resolve eq13 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq89 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq83
    | (have j0 := eq83 X0 X1
       grind)
    | exact resolve eq83 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq92 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq89
    | (have j0 := eq89 X0 X1
       grind)
    | exact resolve eq89 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq89
  have eq248 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq92 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq92
    | (have j0 := eq92 X1 X1
       grind)
    | exact resolve eq92 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq264 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq248 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq248
    | (have j0 := eq248 X0 X1
       grind)
    | exact resolve eq248 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq270 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq264 X0 X1
       have j1 := eq79 X1 X0
       grind)
    | (have r₁ := eq264 X0 X0
       have r₂ := eq79 X0 X1
       grind)
    | exact resolve eq264 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq365 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq270 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq270
    | exact resolve eq270 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq376 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq270 (σ X1) X0
       grind)
    | exact superpose eq270 eq15
    | (have j1 := eq270 (σ X1) X0
       grind)
    | exact resolve eq15 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq389 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq365 X0 X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq365
    | (have j0 := eq365 X0 X1
       grind)
    | exact resolve eq365 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq409 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq389 X0 (τ X1)
       grind)
    | exact superpose eq389 eq17
    | (have j1 := eq389 X0 (τ X1)
       grind)
    | exact resolve eq17 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq389
  have eq1047 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq409 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq409
    | exact resolve eq409 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq1103 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1047 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1047
    | (have j0 := eq1047 X0 X1
       grind)
    | exact resolve eq1047 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047
  have eq3607 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq376 x y
       grind)
    | exact superpose eq376 eq16
    | (have j1 := eq376 x y
       grind)
    | exact resolve eq16 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3628 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq376 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq3785 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq3607
       have i₂ := eq1103 y x
       grind)
    | exact superpose eq1103 eq3607
    | (have j1 := eq1103 y x
       grind)
    | (have r₁ := eq3607
       have r₂ := eq1103 y x
       grind)
    | exact resolve eq3607 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3607
  have eq3786 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3785
  have eq3792 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq3786
       grind)
    | exact superpose eq3786 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3786
       grind)
    | exact resolve eq13 eq3786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3786
  have eq3794 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ (k y x) = (M.op x x) := by grind
  clear eq3792
  have eq3837 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3628 (τ X1) (τ X0)
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq3628
    | (have j0 := eq3628 (τ X1) (τ X0)
       grind)
    | exact resolve eq3628 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq3886 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3837 X0 X1
       have i₂ := eq68 X1
       grind)
    | exact superpose eq68 eq3837
    | (have j0 := eq3837 X0 X1
       grind)
    | exact resolve eq3837 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3837
  have eq3907 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3886 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq3886
    | (have j0 := eq3886 X0 X1
       grind)
    | exact resolve eq3886 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3886
  have eq3921 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3907 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3907
    | (have j0 := eq3907 X0 X1
       grind)
    | exact resolve eq3907 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3907
  have eq3932 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3921 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3921
    | (have j0 := eq3921 X0 X1
       grind)
    | exact resolve eq3921 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3921
  have eq3937 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3932 X0 X1
       have i₂ := eq68 X1
       grind)
    | exact superpose eq68 eq3932
    | (have j0 := eq3932 X0 X1
       grind)
    | exact resolve eq3932 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq3932
  have eq13526 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq78 x (σ y)
       have i₂ := eq3794
       grind)
    | exact superpose eq3794 eq78
    | (have j0 := eq78 x (σ y)
       grind)
    | (have r₁ := eq78 x (σ y)
       have r₂ := eq3794
       grind)
    | exact resolve eq78 eq3794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13533 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ (k y x) = (M.op x x) := by grind
  clear eq13526
  have eq13535 : (k y x) = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13533
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq13533
    | exact resolve eq13533 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13533
  have eq2398099 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3628 x y
       have i₂ := eq13535
       grind)
    | exact superpose eq13535 eq3628
    | (have j0 := eq3628 x y
       grind)
    | (have r₁ := eq3628 x y
       have r₂ := eq13535
       grind)
    | exact resolve eq3628 eq13535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13535
  have eq2398461 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq2398099
  have eq2398476 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq3628 x y
       grind)
    | (have r₁ := eq2398461
       have r₂ := eq3628 x y
       grind)
    | exact resolve eq2398461 eq3628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3628 eq2398461
  have eq2400317 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2398476
       grind)
    | exact superpose eq2398476 eq16
    | exact resolve eq16 eq2398476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2400328 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq78 x (σ y)
       have i₂ := eq2398476
       grind)
    | exact superpose eq2398476 eq78
    | (have j0 := eq78 x (σ y)
       grind)
    | (have r₁ := eq78 x (σ y)
       have r₂ := eq2398476
       grind)
    | exact resolve eq78 eq2398476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq2398476
  have eq2400520 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq2400328
  have eq2400521 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq2400520
  have eq2400567 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2400521
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2400521
    | exact resolve eq2400521 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2400521
  have eq2405563 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq79 x X0
       have i₂ := eq2400567
       grind)
    | exact superpose eq2400567 eq79
    | (have j0 := eq79 x X0
       grind)
    | (have r₁ := eq79 x x
       have r₂ := eq2400567
       grind)
    | exact resolve eq79 eq2400567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2400567
  have eq2405700 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    intro X0
    first
    | (have j0 := eq2405563 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2405563
  have eq2405715 : ∀ X0 : G, (σ (k y x)) = (σ (M.op x x)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq2405700 X0
       have j1 := eq79 x X0
       grind)
    | (have r₁ := eq2405700 X0
       have r₂ := eq79 x x
       grind)
    | exact resolve eq2405700 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2405700
  have eq2405800 : ∀ X0 : G, (k y x) = (τ (σ (M.op x x))) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq2405715 X0
       grind)
    | exact superpose eq2405715 eq10
    | (have j1 := eq2405715 X0
       grind)
    | exact resolve eq10 eq2405715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2405715
  have eq2406528 : ∀ X0 : G, (k y x) = (M.op x x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq2405800 X0
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq2405800
    | (have j0 := eq2405800 X0
       grind)
    | exact resolve eq2405800 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2405800
  have eq2408512 : ∀ X0 : G, (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq3937 y x
       have i₂ := eq2406528 X0
       grind)
    | exact superpose eq2406528 eq3937
    | (have j0 := eq3937 y x
       have j1 := eq2406528 X0
       grind)
    | (have r₁ := eq3937 y x
       have r₂ := eq2406528 X0
       grind)
    | (have r₁ := eq3937 (σ x) (σ x)
       have r₂ := eq2406528 (σ x)
       grind)
    | exact resolve eq3937 eq2406528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3937 eq2406528
  have eq2408870 : ∀ X0 : G, (M.op x y) = (M.op x x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq2408512 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2408512
  have eq2408891 : ∀ X0 : G, (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq2400317
       have i₂ := eq2408870 X0
       grind)
    | exact superpose eq2408870 eq2400317
    | (have j1 := eq2408870 X0
       grind)
    | exact resolve eq2400317 eq2408870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2400317 eq2408870
  have eq2408902 : ∀ X0 : G, (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq2408891 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2408891
  have eq2408913 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq2408902 X0
       have j1 := eq79 x X0
       grind)
    | (have r₁ := eq2408902 X0
       have r₂ := eq79 x x
       grind)
    | exact resolve eq2408902 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2408902
  have eq2410968 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (k X1 (σ x)) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq79 x X0
       have i₂ := eq2408913 X1
       grind)
    | exact superpose eq2408913 eq79
    | (have j0 := eq79 x X0
       have j1 := eq2408913 X0
       grind)
    | exact resolve eq79 eq2408913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq2408913
  have eq2411105 : ∀ X0 X1 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (k X1 (σ x)) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | (have j0 := eq2410968 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2410968
  have eq2419781 : ∀ X0 : G, (M.op (σ x) X0) ≠ (M.op (σ x) X0) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq2411105 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2411105
  have eq2419782 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq2419781 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2419781
  have eq2422012 : ∀ X0 : G, (k (τ X0) x) = (τ (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq24 X0 x
       have i₂ := eq2419782 X0
       grind)
    | exact superpose eq2419782 eq24
    | exact resolve eq24 eq2419782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq2422182 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq2419782 (σ X0)
       grind)
    | exact superpose eq2419782 eq15
    | exact resolve eq15 eq2419782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2419782
  have eq2424043 : (τ (σ (M.op x x))) = (k (τ (σ y)) x) ∨ x = (M.op x x) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq2422012 (σ y)
       have i₂ := eq3794
       grind)
    | exact superpose eq3794 eq2422012
    | exact resolve eq2422012 eq3794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3794 eq2422012
  have eq2426490 : (k y x) = (τ (σ (M.op x x))) ∨ x = (M.op x x) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq2424043
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2424043
    | exact resolve eq2424043 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2424043
  have eq2427042 : (k y x) = (M.op x x) ∨ x = (M.op x x) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq2426490
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq2426490
    | exact resolve eq2426490 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2426490
  have eq2427043 : (k y x) = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq2427042
  have eq2430951 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2422182 y
       grind)
    | exact superpose eq2422182 eq16
    | exact resolve eq16 eq2422182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2422182
  have eq2433322 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2430951
       have i₂ := eq1103 y x
       grind)
    | exact superpose eq1103 eq2430951
    | (have j1 := eq1103 y x
       grind)
    | (have r₁ := eq2430951
       have r₂ := eq1103 y x
       grind)
    | exact resolve eq2430951 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103
  have eq2433323 : (M.op x y) = (M.op x x) := by grind
  clear eq2433322
  have eq2440851 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2430951
       have i₂ := eq2427043
       grind)
    | exact superpose eq2427043 eq2430951
    | exact resolve eq2430951 eq2427043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2427043
  have eq2441277 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2440851
       have i₂ := eq2433323
       grind)
    | exact superpose eq2433323 eq2440851
    | exact resolve eq2440851 eq2433323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2433323 eq2440851
  have eq2441278 : x = (M.op x x) := by grind
  clear eq2441277
  have eq2443763 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq2441278
       grind)
    | exact superpose eq2441278 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq2441278
       grind)
    | exact resolve eq12 eq2441278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2441278
  have eq2443904 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq2443763 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2443763
  have eq2445156 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq2430951
       have i₂ := eq2443904 y
       grind)
    | exact superpose eq2443904 eq2430951
    | exact resolve eq2430951 eq2443904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2430951 eq2443904
  have eq2445157 : False := by grind
  exact eq2445157

/-- `Equation2533`: `x = (y ◇ ((y ◇ x) ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation2533 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2533 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2533.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq269 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq269 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq272 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq270 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq270 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq270 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq283 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq272 (σ X0)
       grind)
    | exact superpose eq272 eq15
    | exact resolve eq15 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq302 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq283 X0
       have i₂ := eq272 X0
       grind)
    | exact superpose eq272 eq283
    | exact resolve eq283 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272 eq283
  have eq347 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq302 X0
       grind)
    | exact superpose eq302 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq302 X0
       grind)
    | exact superpose eq302 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq350 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq347 X0 X1
       have j1 := eq349 X0 X1
       grind)
    | (have r₁ := eq347 X0 X1
       have r₂ := eq349 X0 X1
       grind)
    | exact resolve eq347 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347 eq349
  have eq393 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq350 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq350
    | exact resolve eq350 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq397 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq350 x (σ y)
       grind)
    | exact superpose eq350 eq16
    | (have j1 := eq350 x (σ y)
       grind)
    | exact resolve eq16 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq415 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq397
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq397
    | exact resolve eq397 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq422 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq393 X0 X1
       grind)
    | exact superpose eq393 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq393 X0 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq393 X0 X1
       grind)
    | exact resolve eq13 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq441 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq422 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq449 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq441 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq441 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq441 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq521 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq449 X0 (τ X1)
       grind)
    | exact superpose eq449 eq17
    | (have j1 := eq449 X0 (τ X1)
       grind)
    | exact resolve eq17 eq449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq527 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq449 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq983 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq521 (τ X0) X1
       grind)
    | exact superpose eq521 eq18
    | (have j1 := eq521 (τ X0) X1
       grind)
    | exact resolve eq18 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq521
  have eq990 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq983 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq983
    | (have j0 := eq983 X0 X1
       grind)
    | exact resolve eq983 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq983
  have eq1007 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq990 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq990
    | (have j0 := eq990 X0 X1
       grind)
    | exact resolve eq990 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990
  have eq1012 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1007 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1007
    | (have j0 := eq1007 X0 X1
       grind)
    | exact resolve eq1007 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007
  have eq1080 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1012 X0 X1
       have i₂ := eq449 X0 X1
       grind)
    | exact superpose eq449 eq1012
    | (have j0 := eq1012 X0 X1
       have j1 := eq449 X0 X1
       grind)
    | exact resolve eq1012 eq449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449 eq1012
  have eq1148 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1080 X0 X1
       have j1 := eq527 X1 X0
       grind)
    | (have r₁ := eq1080 X1 X0
       have r₂ := eq527 X0 X1
       grind)
    | exact resolve eq1080 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527 eq1080
  have eq1194 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (σ (M.op (τ (σ X0)) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq1148 (σ X0) X1
       grind)
    | exact superpose eq1148 eq22
    | (have j1 := eq1148 (σ X0) X1
       grind)
    | exact resolve eq22 eq1148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1148
  have eq1230 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op (σ X0) X1) = (σ (M.op (τ (σ X0)) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1194 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1194
    | (have j0 := eq1194 X0 X1
       grind)
    | exact resolve eq1194 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194
  have eq1251 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1230 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1230
    | (have j0 := eq1230 X0 X1
       grind)
    | exact resolve eq1230 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230
  have eq1553 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1251 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1251
    | exact resolve eq1251 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251
  have eq1635 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1553 y x
       grind)
    | exact superpose eq1553 eq16
    | (have j1 := eq1553 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq1553 y x
       grind)
    | exact resolve eq16 eq1553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1553
  have eq1658 : x = (k y x) := by grind
  clear eq1635
  have eq1791 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq415
       have i₂ := eq393 x y
       grind)
    | exact superpose eq393 eq415
    | (have j1 := eq393 x y
       grind)
    | exact resolve eq415 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1792 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by grind
  clear eq1791
  have eq1793 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1792
       have i₂ := eq1658
       grind)
    | exact superpose eq1658 eq1792
    | exact resolve eq1792 eq1658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1792
  have eq1794 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1793
       have i₂ := eq1658
       grind)
    | exact superpose eq1658 eq1793
    | exact resolve eq1793 eq1658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1793
  have eq1795 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq415
       have i₂ := eq1794
       grind)
    | exact superpose eq1794 eq415
    | exact resolve eq415 eq1794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415 eq1794
  have eq1803 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1795
  have eq1804 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1803
       have i₂ := eq1658
       grind)
    | exact superpose eq1658 eq1803
    | exact resolve eq1803 eq1658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1803
  have eq1805 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1804
  have eq1807 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1805
       grind)
    | exact superpose eq1805 eq16
    | exact resolve eq16 eq1805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1805
  have eq1824 : (σ x) ≠ (σ x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1807
       have i₂ := eq393 x y
       grind)
    | exact superpose eq393 eq1807
    | (have j1 := eq393 x y
       grind)
    | exact resolve eq1807 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq1825 : (M.op x y) = (k y x) := by grind
  clear eq1824
  have eq1827 : x = (M.op x y) := by
    first
    | (have i₁ := eq1825
       have i₂ := eq1658
       grind)
    | exact superpose eq1658 eq1825
    | exact resolve eq1825 eq1658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1658 eq1825
  have eq1828 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1807
       have i₂ := eq1827
       grind)
    | exact superpose eq1827 eq1807
    | exact resolve eq1807 eq1827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1807 eq1827
  have eq1838 : False := by grind
  exact eq1838

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_pyy_pxx_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq50 : ∀ X0 : G, y = (M.op (M.op x (M.op (M.op x y) X0)) y) := by
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
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 X0) X2)) ≠ X0 ∨ (k X0 (M.op X1 (M.op (M.op X1 X0) X2))) = (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X1 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op X1 (M.op (M.op X1 X0) X2))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 (M.op X1 (M.op (M.op X1 X0) X2))
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq95
    | exact resolve eq95 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq167 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq455 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq462 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq52 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 x X0 X1 y
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq464 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ x)) X1)) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq466 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq469 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq466 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq466
    | exact resolve eq466 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq472 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq455 X0 x x X3 X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq455
    | exact resolve eq455 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq478 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq469 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq469
    | (have j0 := eq469 x y
       grind)
    | exact resolve eq469 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq480 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq469
    | (have j0 := eq469 (σ x) (σ y)
       grind)
    | exact resolve eq469 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq496 : ∀ X0 : G, (M.op x y) = (M.op (M.op x (M.op (M.op x y) X0)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq478 eq14
    | exact resolve eq14 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq598 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq75 X1 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq75 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq75 X0 X1
       grind)
    | exact resolve eq13 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq601 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq75 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq603 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq601 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq606 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq598 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq598 X0 X1
       have r₂ := eq13 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq598 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq598 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq615 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq606 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq606
    | (have j0 := eq606 X0 X1
       grind)
    | exact resolve eq606 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq728 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) (M.op X0 X4)) ≠ X0 ∨ (k X0 (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) (M.op X0 X4))) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) (M.op X0 X4)) (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) (M.op X0 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq65 X0 (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X2
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq65
    | exact resolve eq65 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq741 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) ≠ (M.op X0 X3) ∨ (k (M.op X0 X3) (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0)) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq65 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq65
    | exact resolve eq65 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq751 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) ≠ X0 ∨ (k (M.op X0 X3) (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0)) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq741 X0 X1 X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq741
    | (have j0 := eq741 X0 X1 X2 X3
       grind)
    | exact resolve eq741 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq756 : ∀ X0 X3 : G, (M.op X0 X3) ≠ X0 ∨ (M.op X0 X0) = (k (M.op X0 X3) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq751 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq751
    | (have j0 := eq751 X0 x x X3
       grind)
    | exact resolve eq751 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq3250 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 X0 x X0
       have i₂ := eq472 X0 X0 x
       grind)
    | exact superpose eq472 eq52
    | exact resolve eq52 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3289 : x = (M.op (M.op (M.op x x) (M.op x y)) x) := by
    first
    | (have i₁ := eq462 x x
       have i₂ := eq3250 x
       grind)
    | exact superpose eq3250 eq462
    | exact resolve eq462 eq3250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq3290 : (σ x) = (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq464 sF2 sF2
       have i₂ := eq3250 sF2
       grind)
    | exact superpose eq3250 eq464
    | exact resolve eq464 eq3250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq3291 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq472 X0 X0 X0
       have i₂ := eq3250 X0
       grind)
    | exact superpose eq3250 eq472
    | exact resolve eq472 eq3250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472 eq3250
  have eq3348 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq603 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq603
    | (have j0 := eq603 (τ X0)
       grind)
    | exact resolve eq603 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq603
  have eq3356 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3348 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3348
    | (have j0 := eq3348 X0
       grind)
    | exact resolve eq3348 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3348
  have eq3362 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3356 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3356
    | (have j0 := eq3356 X0
       grind)
    | exact resolve eq3356 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3356
  have eq3713 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq756 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq3291 X0
       grind)
    | exact superpose eq3291 eq756
    | (have r₁ := eq756 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq3291 X0
       grind)
    | exact resolve eq756 eq3291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3291
  have eq3715 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq3713 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3713
  have eq3830 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq167 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq167
    | (have j0 := eq167 x
       grind)
    | exact resolve eq167 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq3846 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3830
  have eq3851 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3846
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq3846
    | exact resolve eq3846 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq3846
  have eq3868 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq3851
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq3851 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3851
  have eq3874 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq3868 eq49
    | exact resolve eq49 eq3868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq3868
  have eq14690 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq97 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq14697 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq14690
    | exact resolve eq14690 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14690
  have eq14708 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq14697
       have r₂ := eq27
       grind)
    | exact resolve eq14697 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14697
  have eq14710 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq14708
    | exact resolve eq14708 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14708
  have eq14713 : (τ (σ x)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq14710 eq3874
    | exact resolve eq3874 eq14710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14710
  have eq14784 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq14713
    | exact resolve eq14713 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14713
  have eq14796 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq3362 x
       grind)
    | (have r₁ := eq14784
       have r₂ := eq3362 x
       grind)
    | exact resolve eq14784 eq3362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3362 eq14784
  have eq14799 : x = (M.op (M.op x (M.op x y)) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3289
       have i₂ := eq14796
       grind)
    | exact superpose eq14796 eq3289
    | exact resolve eq3289 eq14796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3289
  have eq14801 : x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3715 x
       have i₂ := eq14796
       grind)
    | exact superpose eq14796 eq3715
    | exact resolve eq3715 eq14796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14855 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq478 eq14799
    | exact resolve eq14799 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14799
  have eq14884 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq615 x x
       have i₂ := eq14801
       grind)
    | exact superpose eq14801 eq615
    | (have j0 := eq615 x x
       grind)
    | exact resolve eq615 eq14801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14801
  have eq14887 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14884
  have eq14888 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14887
  have eq14900 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14888
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14888
    | exact resolve eq14888 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14888
  have eq14936 : y = (M.op (M.op x x) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14855 eq50
    | exact resolve eq50 eq14855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq14855
  have eq14974 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14900 eq3290
    | exact resolve eq3290 eq14900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3290
  have eq15047 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq480 eq14974
    | exact resolve eq14974 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14974
  have eq15061 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15047 eq51
    | exact resolve eq51 eq15047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15047
  have eq15598 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14936
       have i₂ := eq14796
       grind)
    | exact superpose eq14796 eq14936
    | exact resolve eq14936 eq14796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14796 eq14936
  have eq15634 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15598
  have eq15648 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15634
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15634
    | exact resolve eq15634 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15634
  have eq15652 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15648 eq51
    | exact resolve eq51 eq15648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15653 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15648 eq64
    | (have r₁ := eq64
       have r₂ := eq15648
       grind)
    | exact resolve eq64 eq15648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq15661 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15648 eq480
    | exact resolve eq480 eq15648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15672 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq15653
  have eq15681 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq15652 X0
       have i₂ := eq469 sF2 (M.op sF2 X0)
       grind)
    | (have i₁ := eq15652 x
       have i₂ := eq469 sF2 x
       grind)
    | exact superpose eq469 eq15652
    | exact resolve eq15652 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15652
  have eq15818 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15661 eq3874
    | exact resolve eq3874 eq15661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15889 : x = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq15818
    | exact resolve eq15818 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq15818
  have eq16049 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq15889
       grind)
    | exact superpose eq15889 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq15889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15889
  have eq16064 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq16049
  have eq16310 : ∀ X0 X1 X2 : G, x ≠ (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x X2)) x) ∨ (k x (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x X2)) x)) = (M.op (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x X2)) x) (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x X2)) x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq728 x X1 X2 x x
       have i₂ := eq16064
       grind)
    | exact superpose eq16064 eq728
    | exact resolve eq728 eq16064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728 eq16064
  have eq16318 : ∀ X0 X1 X2 : G, (k x (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x X2)) x)) = (M.op (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x X2)) x) (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x X2)) x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have j0 := eq16310 X0 X1 X2
       grind)
    | (have r₁ := eq16310 X1 X2 x
       have r₂ := eq52 x X1 X2 x
       grind)
    | exact resolve eq16310 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16310
  have eq16341 : (k x x) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16318 x x x
       have i₂ := eq52 x x x x
       grind)
    | exact superpose eq52 eq16318
    | exact resolve eq16318 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq16318
  have eq16758 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14900 eq15061
    | exact resolve eq15061 eq14900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14900 eq15061
  have eq16796 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16758
  have eq16811 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq16796
    | exact resolve eq16796 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16796
  have eq16814 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16811 eq27
    | exact resolve eq27 eq16811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16811
  have eq16991 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15661 eq15681
    | exact resolve eq15681 eq15661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15661 eq15681
  have eq17045 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq16991
  have eq17063 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq17045
    | exact resolve eq17045 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17045
  have eq17090 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17063 eq15648
    | exact resolve eq15648 eq17063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17093 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq17090
  have eq17099 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17093 eq26
    | exact resolve eq26 eq17093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17093
  have eq18146 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17099 eq756
    | (have j0 := eq756 (σ x) (σ y)
       grind)
    | (have r₁ := eq756 x y
       have r₂ := eq17099
       grind)
    | exact resolve eq756 eq17099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756 eq17099
  have eq18161 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq18146
       have r₂ := eq15648
       grind)
    | exact resolve eq18146 eq15648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15648 eq18146
  have eq18484 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17063 eq18161
    | exact resolve eq18161 eq17063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17063 eq18161
  have eq18497 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq18484
  have eq18627 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18497 eq15672
    | exact resolve eq15672 eq18497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15672 eq18497
  have eq18635 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq18627
  have eq18762 : (τ (σ y)) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18635 eq3874
    | exact resolve eq3874 eq18635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3874 eq18635
  have eq18840 : y = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq18762
    | exact resolve eq18762 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq18762
  have eq22657 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18840
       have i₂ := eq16341
       grind)
    | exact superpose eq16341 eq18840
    | exact resolve eq18840 eq16341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16341 eq18840
  have eq22672 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq22657
  have eq22746 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq469 x x
       have i₂ := eq22672
       grind)
    | exact superpose eq22672 eq469
    | exact resolve eq469 eq22672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22672
  have eq22769 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq22746
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22746
    | exact resolve eq22746 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22746
  have eq22770 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq22769
  have eq22772 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22770 eq20
    | exact resolve eq20 eq22770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22770
  have eq22916 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22772
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq22772
    | exact resolve eq22772 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22772
  have eq23093 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22916 eq16814
    | (have r₁ := eq16814
       have r₂ := eq22916
       grind)
    | exact resolve eq16814 eq22916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16814
  have eq23121 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23093
  have eq23122 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq23121
  have eq23198 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ x) X0)) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq23122 eq51
    | exact resolve eq51 eq23122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq23207 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23122 eq480
    | exact resolve eq480 eq23122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480 eq23122
  have eq23260 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq23198 X0
       have i₂ := eq469 sF2 (M.op sF2 X0)
       grind)
    | (have i₁ := eq23198 x
       have i₂ := eq469 sF2 x
       grind)
    | exact superpose eq469 eq23198
    | exact resolve eq23198 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23198
  have eq25744 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23207 eq23260
    | exact resolve eq23260 eq23207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23207 eq23260
  have eq25808 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq25744
  have eq25837 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq25808
    | exact resolve eq25808 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25808
  have eq25847 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25837 eq27
    | exact resolve eq27 eq25837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25837
  have eq25919 : x = (M.op x y) := by
    first
    | (have r₁ := eq25847
       have r₂ := eq22916
       grind)
    | exact resolve eq25847 eq22916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22916 eq25847
  have eq25923 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq25919 eq20
    | exact resolve eq20 eq25919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq25987 : x = (M.op x x) := by
    first
    | exact superpose eq25919 eq478
    | exact resolve eq478 eq25919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq25989 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | exact superpose eq25919 eq496
    | exact resolve eq496 eq25919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496
  have eq26011 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq25989 X0
       have i₂ := eq469 x X0
       grind)
    | (have i₁ := eq25989 X0
       have i₂ := eq469 x (M.op x X0)
       grind)
    | exact superpose eq469 eq25989
    | exact resolve eq25989 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469 eq25989
  have eq26070 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq25923
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25923
    | exact resolve eq25923 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25923
  have eq26186 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq26070 eq26
    | exact resolve eq26 eq26070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq26387 : x = (k x x) := by
    first
    | (have i₁ := eq3715 x
       have i₂ := eq25987
       grind)
    | exact superpose eq25987 eq3715
    | exact resolve eq3715 eq25987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3715
  have eq26809 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq615 x x
       have i₂ := eq26387
       grind)
    | exact superpose eq26387 eq615
    | (have j0 := eq615 x x
       grind)
    | exact resolve eq615 eq26387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615 eq26387
  have eq26812 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq26809
  have eq26813 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq26812
  have eq26825 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26813
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq26813
    | exact resolve eq26813 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26813
  have eq26840 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq26070 eq26825
    | exact resolve eq26825 eq26070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26825
  have eq27941 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x x
       have i₂ := eq26011 X0
       grind)
    | exact superpose eq26011 eq14
    | exact resolve eq14 eq26011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26011
  have eq27999 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq27941 X0
       have i₂ := eq25987
       grind)
    | exact superpose eq25987 eq27941
    | exact resolve eq27941 eq25987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25987 eq27941
  have eq28036 : y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq27999 y
       grind)
    | exact superpose eq27999 eq18
    | (have j1 := eq27999 y
       grind)
    | exact resolve eq18 eq27999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq27999
  have eq28138 : x = y := by
    first
    | exact superpose eq25919 eq28036
    | exact resolve eq28036 eq25919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25919 eq28036
  have eq28185 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq28138
       grind)
    | exact superpose eq28138 eq24
    | exact resolve eq24 eq28138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq28138
  have eq28331 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq28185
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28185
    | exact resolve eq28185 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq28185
  have eq28396 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26070 eq28331
    | exact resolve eq28331 eq26070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26070 eq28331
  have eq28734 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq28396 eq26186
    | exact resolve eq26186 eq28396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26186 eq28396
  have eq28739 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26840 eq28734
    | exact resolve eq28734 eq26840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26840 eq28734
  have eq28805 : False := by grind
  exact eq28805

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pxx_y_pxy_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  clear eq39
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
  have eq174 : ∀ X0 : G, y = (M.op (M.op x (M.op (M.op x y) X0)) y) := by
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
  have eq175 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, y = (M.op (M.op (M.op x (M.op (M.op x y) X0)) (M.op y X1)) y) := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (M.op (σ y) X1)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op (M.op x (M.op (M.op x y) X0)) y) (M.op y X1)) := by
    intro X0 X1
    first
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq544 : ∀ X1 : G, (M.op y X1) = (M.op y (M.op y X1)) := by
    intro X1
    first
    | exact superpose eq174 eq542
    | exact resolve eq542 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq884 : (M.op x y) = (k x y) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
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
  have eq894 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq905 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq906 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq905 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq929 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq906 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq906
    | (have j0 := eq906 (σ X0)
       grind)
    | exact resolve eq906 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1865 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq176 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq176 X0 X1 X2 X3
       grind)
    | exact superpose eq176 eq176
    | exact resolve eq176 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1879 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 (M.op (M.op X0 x) X1)) (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq176 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq176
    | (have j0 := eq176 x X0 X1 y
       grind)
    | exact resolve eq176 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1882 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 (M.op (M.op X0 (σ x)) X1)) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq176
    | (have j0 := eq176 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1887 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq176 X0 X1 X2 X3
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1891 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq1887 X0 x x X3
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq1887
    | exact resolve eq1887 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1887
  have eq1897 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq1865 X0 x x X3 X4
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq1865
    | exact resolve eq1865 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1865
  have eq1941 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq1891
    | (have j0 := eq1891 (σ x) (σ y)
       grind)
    | exact resolve eq1891 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5932 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq884
       grind)
    | exact superpose eq884 eq40
    | exact resolve eq40 eq884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq884
  have eq5933 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq5932
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5932
    | exact resolve eq5932 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5932
  have eq5937 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq5933
    | exact resolve eq5933 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5933
  have eq15298 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq5937 eq894
    | exact resolve eq894 eq5937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894 eq5937
  have eq15306 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq15298
       have r₂ := eq27
       grind)
    | exact resolve eq15298 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15298
  have eq15316 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq15306 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq15306
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq15306
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq15306
       grind)
    | exact resolve eq13 eq15306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15324 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq15316 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15316
  have eq15370 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq15306
       have i₂ := eq15324 sF3
       grind)
    | exact superpose eq15324 eq15306
    | exact resolve eq15306 eq15324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15306 eq15324
  have eq15384 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq15370
  have eq15403 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq15384 eq152
    | exact resolve eq152 eq15384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq15384
  have eq15415 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq31 eq15403
    | exact resolve eq15403 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq15403
  have eq15420 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq906 (σ x)
       grind)
    | (have r₁ := eq15415
       have r₂ := eq906 y
       grind)
    | exact resolve eq15415 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15415
  have eq15427 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq15420 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq15420
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq15420
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq15420
       grind)
    | exact resolve eq13 eq15420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15435 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq15427 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15427
  have eq15485 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq15420
       have i₂ := eq15435 sF2
       grind)
    | exact superpose eq15435 eq15420
    | exact resolve eq15420 eq15435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15420 eq15435
  have eq15500 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq15485
  have eq15521 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq15500 eq141
    | exact resolve eq141 eq15500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq15500
  have eq15533 : x = (k x x) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq15521
    | exact resolve eq15521 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq15521
  have eq15538 : y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq906 y
       grind)
    | (have r₁ := eq15533
       have r₂ := eq906 x
       grind)
    | exact resolve eq15533 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906 eq15533
  have eq15547 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq15538
       grind)
    | exact superpose eq15538 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq15538
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq15538
       grind)
    | exact resolve eq13 eq15538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15554 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1897 y y x
       have i₂ := eq15538
       grind)
    | exact superpose eq15538 eq1897
    | exact resolve eq1897 eq15538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15555 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq15547 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15547
  have eq15560 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq15554 X0
       have i₂ := eq544 X0
       grind)
    | (have i₁ := eq15554 X0
       have i₂ := eq544 (M.op y X0)
       grind)
    | exact superpose eq544 eq15554
    | exact resolve eq15554 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544 eq15554
  have eq15599 : y = (k y y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq15538
       have i₂ := eq15555 y
       grind)
    | exact superpose eq15555 eq15538
    | exact resolve eq15538 eq15555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15625 : y = (k y y) ∨ x = (M.op x x) := by grind
  clear eq15599
  have eq15651 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq929 y
       have i₂ := eq15625
       grind)
    | exact superpose eq15625 eq929
    | (have j0 := eq929 y
       grind)
    | exact resolve eq929 eq15625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15625
  have eq15658 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq15651
  have eq15660 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq15658
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15658
    | exact resolve eq15658 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15658
  have eq15672 : (σ y) = (k (σ y) y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq15660 eq15555
    | exact resolve eq15555 eq15660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15660
  have eq15688 : (σ y) = (k (σ y) y) ∨ x = (M.op x x) := by grind
  clear eq15672
  have eq15749 : x = (M.op (M.op (M.op y y) (M.op x y)) x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1879 y y
       have i₂ := eq15560 x
       grind)
    | exact superpose eq15560 eq1879
    | exact resolve eq1879 eq15560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1879
  have eq15755 : ∀ X0 X1 : G, (M.op (M.op (M.op y y) (M.op X0 X1)) X0) = X0 ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq176 X0 y y X1
       have i₂ := eq15560 X0
       grind)
    | exact superpose eq15560 eq176
    | exact resolve eq176 eq15560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15756 : ∀ X0 : G, (M.op (M.op y y) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y y
       have i₂ := eq15560 X0
       grind)
    | exact superpose eq15560 eq16
    | exact resolve eq16 eq15560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15560
  have eq15772 : ∀ X0 : G, x = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | exact superpose eq15538 eq15756
    | exact resolve eq15756 eq15538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15756
  have eq15773 : ∀ X0 X1 : G, (M.op (M.op y (M.op X0 X1)) X0) = X0 ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq15538 eq15755
    | exact resolve eq15755 eq15538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15755
  have eq15777 : x = (M.op (M.op y (M.op x y)) x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq15538 eq15749
    | exact resolve eq15749 eq15538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15538 eq15749
  have eq15779 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq15772 eq15773
    | exact resolve eq15773 eq15772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15773
  have eq15781 : x = (M.op (M.op x y) x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq15772 eq15777
    | exact resolve eq15777 eq15772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15777
  have eq15956 : y = (M.op (M.op x x) y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq15781 eq174
    | exact resolve eq174 eq15781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq15987 : y = (M.op (k x y) y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq15555 eq15956
    | exact resolve eq15956 eq15555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15956
  have eq16064 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X0
       have i₂ := eq15779 X0 X1
       grind)
    | exact superpose eq15779 eq16
    | exact resolve eq16 eq15779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15779
  have eq16098 : ∀ X0 X1 : G, (M.op (k X0 y) X1) = X1 ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq15555 eq16064
    | exact resolve eq16064 eq15555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15555 eq16064
  have eq16604 : ∀ X0 X1 : G, y = (M.op (M.op (M.op (k x y) (M.op y X0)) (M.op y X1)) y) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq176 y (k x y) X0 X1
       have i₂ := eq15987
       grind)
    | exact superpose eq15987 eq176
    | exact resolve eq176 eq15987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq15987
  have eq16617 : ∀ X0 X1 : G, y = (M.op (M.op (M.op (k x y) (M.op y X0)) X1) y) ∨ x = (M.op x x) := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f16617_13 : ∀ X0 : G, x = (M.op x x) ∨ (M.op y X0) = X0 := by
      intro X0
      grind
    have f16617_20 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
      intro X0 X1 X2
      grind
    have f16617_21 : y ≠ (M.op (M.op (M.op (k x y) (M.op y X0)) X1) y) := by grind
    have f16617_22 : x ≠ (M.op x x) := by grind
    have f16617_23 : ∀ X0 : G, (M.op y X0) = X0 := by
      intro X0
      first
      | (have j0 := f16617_13 X0
         grind)
      | (have r₁ := f16617_13 X0
         have r₂ := f16617_22
         grind)
      | exact resolve f16617_13 f16617_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f16617_36 : ∀ X0 X1 : G, (M.op (M.op (M.op y X0) X1) X0) = X0 := by
      intro X0 X1
      first
      | (have i₁ := f16617_20 X0 y X1
         have i₂ := f16617_23 (M.op (M.op y X0) X1)
         grind)
      | exact superpose f16617_23 f16617_20
      | exact resolve f16617_20 f16617_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f16617_37 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
      intro X0 X1
      first
      | (have i₁ := f16617_36 X0 X1
         have i₂ := f16617_23 X0
         grind)
      | exact superpose f16617_23 f16617_36
      | exact resolve f16617_36 f16617_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f16617_39 : ∀ X0 : G, y = (M.op X0 y) := by
      intro X0
      first
      | (have i₁ := f16617_37 y X0
         have i₂ := f16617_23 X0
         grind)
      | exact superpose f16617_23 f16617_37
      | exact resolve f16617_37 f16617_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f16617_74 : y ≠ y := by
      first
      | (have i₁ := f16617_21
         have i₂ := f16617_39 (M.op (M.op (k x y) (M.op y X0)) X1)
         grind)
      | exact superpose f16617_39 f16617_21
      | (have r₁ := f16617_21
         have r₂ := f16617_39 (M.op (M.op (k x y) (M.op y X0)) X1)
         grind)
      | exact resolve f16617_21 f16617_39
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f16617_75 : False := by grind
    exact f16617_75
  clear eq16604
  have eq16620 : ∀ X0 X1 : G, y = (M.op (M.op (M.op (k x y) X0) X1) y) ∨ x = (M.op x x) := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f16620_13 : ∀ X0 : G, x = (M.op x x) ∨ (M.op y X0) = X0 := by
      intro X0
      grind
    have f16620_20 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
      intro X0 X1 X2
      grind
    have f16620_21 : y ≠ (M.op (M.op (M.op (k x y) X0) X1) y) := by grind
    have f16620_22 : x ≠ (M.op x x) := by grind
    have f16620_23 : ∀ X0 : G, (M.op y X0) = X0 := by
      intro X0
      first
      | (have j0 := f16620_13 X0
         grind)
      | (have r₁ := f16620_13 X0
         have r₂ := f16620_22
         grind)
      | exact resolve f16620_13 f16620_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f16620_35 : ∀ X0 X1 : G, (M.op (M.op (M.op y X0) X1) X0) = X0 := by
      intro X0 X1
      first
      | (have i₁ := f16620_20 X0 y X1
         have i₂ := f16620_23 (M.op (M.op y X0) X1)
         grind)
      | exact superpose f16620_23 f16620_20
      | exact resolve f16620_20 f16620_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f16620_36 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
      intro X0 X1
      first
      | (have i₁ := f16620_35 X0 X1
         have i₂ := f16620_23 X0
         grind)
      | exact superpose f16620_23 f16620_35
      | exact resolve f16620_35 f16620_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f16620_38 : ∀ X0 : G, y = (M.op X0 y) := by
      intro X0
      first
      | (have i₁ := f16620_36 y X0
         have i₂ := f16620_23 X0
         grind)
      | exact superpose f16620_23 f16620_36
      | exact resolve f16620_36 f16620_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f16620_46 : y ≠ y := by
      first
      | (have i₁ := f16620_21
         have i₂ := f16620_38 (M.op (M.op (k x y) X0) X1)
         grind)
      | exact superpose f16620_38 f16620_21
      | (have r₁ := f16620_21
         have r₂ := f16620_38 (M.op (M.op (k x y) X0) X1)
         grind)
      | exact resolve f16620_21 f16620_38
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f16620_47 : False := by grind
    exact f16620_47
  clear eq15772 eq16617
  have eq16621 : ∀ X0 X1 : G, y = (M.op (M.op X0 X1) y) ∨ x = (M.op x x) := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f16621_12 : ∀ X0 X1 : G, y = (M.op (M.op (M.op (k x y) X0) X1) y) ∨ x = (M.op x x) := by
      intro X0 X1
      grind
    have f16621_13 : ∀ X0 X1 : G, (M.op (k X0 y) X1) = X1 ∨ x = (M.op x x) := by
      intro X0 X1
      grind
    have f16621_21 : y ≠ (M.op (M.op X0 X1) y) := by grind
    have f16621_22 : x ≠ (M.op x x) := by grind
    have f16621_23 : ∀ X0 X1 : G, (M.op (k X0 y) X1) = X1 := by
      intro X0 X1
      first
      | (have j0 := f16621_13 X0 X1
         grind)
      | (have r₁ := f16621_13 X0 X1
         have r₂ := f16621_22
         grind)
      | exact resolve f16621_13 f16621_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f16621_24 : ∀ X0 X1 : G, y = (M.op (M.op (M.op (k x y) X0) X1) y) := by
      intro X0 X1
      first
      | (have j0 := f16621_12 X0 X1
         grind)
      | (have r₁ := f16621_12 X0 X1
         have r₂ := f16621_22
         grind)
      | exact resolve f16621_12 f16621_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f16621_25 : ∀ X0 X1 : G, y = (M.op (M.op X0 X1) y) := by
      intro X0 X1
      first
      | (have i₁ := f16621_24 X0 X1
         have i₂ := f16621_23 x X0
         grind)
      | exact superpose f16621_23 f16621_24
      | exact resolve f16621_24 f16621_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f16621_28 : y ≠ y := by
      first
      | (have i₁ := f16621_21
         have i₂ := f16621_25 X0 X1
         grind)
      | exact superpose f16621_25 f16621_21
      | (have r₁ := f16621_21
         have r₂ := f16621_25 X0 X1
         grind)
      | exact resolve f16621_21 f16621_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f16621_29 : False := by grind
    exact f16621_29
  clear eq16620
  have eq16665 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq15688 eq16098
    | exact resolve eq16098 eq15688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15688 eq16098
  have eq16716 : ∀ X0 : G, x = (M.op x x) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq16665 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16665
  have eq17423 : y = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq15781 eq16621
    | exact resolve eq16621 eq15781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15781
  have eq17425 : y = (M.op (M.op (σ x) (σ y)) y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1941 eq16621
    | (have j0 := eq16621 (σ x) (σ y)
       grind)
    | exact resolve eq16621 eq1941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1941
  have eq17444 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = X1 ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 y
       have i₂ := eq16621 X0 X1
       grind)
    | exact superpose eq16621 eq16
    | exact resolve eq16 eq16621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16621
  have eq17464 : y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq17423
  have eq17488 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17464
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17464
    | exact resolve eq17464 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17464
  have eq17509 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1897 x x x
       have i₂ := eq17488
       grind)
    | exact superpose eq17488 eq1897
    | exact resolve eq1897 eq17488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17514 : ∀ X0 : G, x = (M.op (M.op x X0) x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq17509 X0
       have i₂ := eq1891 x X0
       grind)
    | (have i₁ := eq17509 X0
       have i₂ := eq1891 x (M.op x X0)
       grind)
    | exact superpose eq1891 eq17509
    | exact resolve eq17509 eq1891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17509
  have eq17549 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) y) (M.op (σ y) X0)) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq17425 eq182
    | exact resolve eq182 eq17425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq17425
  have eq17574 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) y) X0) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f17574_13 : ∀ X0 : G, x = (M.op x x) ∨ (M.op (σ y) X0) = X0 := by
      intro X0
      grind
    have f17574_20 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
      intro X0 X1 X2
      grind
    have f17574_21 : (σ y) ≠ (M.op (M.op (M.op (σ x) y) X0) (σ y)) := by grind
    have f17574_22 : x ≠ (M.op x x) := by grind
    have f17574_23 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
      intro X0
      first
      | (have j0 := f17574_13 X0
         grind)
      | (have r₁ := f17574_13 X0
         have r₂ := f17574_22
         grind)
      | exact resolve f17574_13 f17574_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f17574_35 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ y) X0) X1) X0) = X0 := by
      intro X0 X1
      first
      | (have i₁ := f17574_20 X0 (σ y) X1
         have i₂ := f17574_23 (M.op (M.op (σ y) X0) X1)
         grind)
      | exact superpose f17574_23 f17574_20
      | exact resolve f17574_20 f17574_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f17574_36 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
      intro X0 X1
      first
      | (have i₁ := f17574_35 X0 X1
         have i₂ := f17574_23 X0
         grind)
      | exact superpose f17574_23 f17574_35
      | exact resolve f17574_35 f17574_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f17574_38 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
      intro X0
      first
      | (have i₁ := f17574_36 (σ y) X0
         have i₂ := f17574_23 X0
         grind)
      | exact superpose f17574_23 f17574_36
      | exact resolve f17574_36 f17574_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f17574_52 : (σ y) ≠ (σ y) := by
      first
      | (have i₁ := f17574_21
         have i₂ := f17574_38 (M.op (M.op (σ x) y) X0)
         grind)
      | exact superpose f17574_38 f17574_21
      | (have r₁ := f17574_21
         have r₂ := f17574_38 (M.op (M.op (σ x) y) X0)
         grind)
      | exact resolve f17574_21 f17574_38
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f17574_53 : False := by grind
    exact f17574_53
  clear eq16716 eq17549
  have eq17576 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f17576_12 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) y) X0) (σ y)) ∨ x = (M.op x x) := by
      intro X0
      grind
    have f17576_13 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = X1 ∨ x = (M.op x x) := by
      intro X0 X1
      grind
    have f17576_21 : (σ y) ≠ (M.op X0 (σ y)) := by grind
    have f17576_22 : x ≠ (M.op x x) := by grind
    have f17576_23 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = X1 := by
      intro X0 X1
      first
      | (have j0 := f17576_13 X0 X1
         grind)
      | (have r₁ := f17576_13 X0 X1
         have r₂ := f17576_22
         grind)
      | exact resolve f17576_13 f17576_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f17576_24 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) y) X0) (σ y)) := by
      intro X0
      first
      | (have j0 := f17576_12 X0
         grind)
      | (have r₁ := f17576_12 X0
         have r₂ := f17576_22
         grind)
      | exact resolve f17576_12 f17576_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f17576_25 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
      intro X0
      first
      | (have i₁ := f17576_24 X0
         have i₂ := f17576_23 (σ x) X0
         grind)
      | exact superpose f17576_23 f17576_24
      | exact resolve f17576_24 f17576_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f17576_27 : (σ y) ≠ (σ y) := by
      first
      | (have i₁ := f17576_21
         have i₂ := f17576_25 X0
         grind)
      | exact superpose f17576_25 f17576_21
      | (have r₁ := f17576_21
         have r₂ := f17576_25 X0
         grind)
      | exact resolve f17576_21 f17576_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f17576_28 : False := by grind
    exact f17576_28
  clear eq17444 eq17574
  have eq17907 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x x
       have i₂ := eq17514 X0
       grind)
    | exact superpose eq17514 eq16
    | exact resolve eq16 eq17514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17514
  have eq17926 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17488 eq17907
    | exact resolve eq17907 eq17488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17488 eq17907
  have eq17998 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq17926 y
       grind)
    | exact superpose eq17926 eq18
    | (have j1 := eq17926 y
       grind)
    | exact resolve eq18 eq17926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq17926
  have eq18034 : y = (M.op x y) := by grind
  clear eq17998
  have eq18054 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq18034
       grind)
    | exact superpose eq18034 eq24
    | exact resolve eq24 eq18034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq18034
  have eq18112 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq18054 eq20
    | exact resolve eq20 eq18054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq18054
  have eq19838 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17576 eq26
    | (have j1 := eq17576 (σ x)
       grind)
    | exact resolve eq26 eq17576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17576
  have eq19895 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k X0 x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq19838
       grind)
    | exact superpose eq19838 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq19838
       grind)
    | exact resolve eq13 eq19838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19904 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1897 x x x
       have i₂ := eq19838
       grind)
    | exact superpose eq19838 eq1897
    | exact resolve eq1897 eq19838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1897
  have eq19906 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq19895 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19895
  have eq19909 : ∀ X0 : G, x = (M.op (M.op x X0) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq19904 X0
       have i₂ := eq1891 x X0
       grind)
    | (have i₁ := eq19904 X0
       have i₂ := eq1891 x (M.op x X0)
       grind)
    | exact superpose eq1891 eq19904
    | exact resolve eq19904 eq1891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1891 eq19904
  have eq20773 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19838
       have i₂ := eq19906 x
       grind)
    | exact superpose eq19906 eq19838
    | exact resolve eq19838 eq19906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20809 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20773
  have eq20850 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq929 x
       have i₂ := eq20809
       grind)
    | exact superpose eq20809 eq929
    | (have j0 := eq929 x
       grind)
    | exact resolve eq929 eq20809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929 eq20809
  have eq20857 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20850
  have eq20859 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20857
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20857
    | exact resolve eq20857 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq20857
  have eq20883 : (σ x) = (k (σ x) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20859 eq19906
    | exact resolve eq19906 eq20859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20859
  have eq20898 : (σ x) = (k (σ x) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20883
  have eq20978 : (σ x) = (M.op (M.op (M.op x x) (M.op (σ x) (σ y))) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1882 x x
       have i₂ := eq19909 sF2
       grind)
    | exact superpose eq19909 eq1882
    | exact resolve eq1882 eq19909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1882
  have eq20979 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x x
       have i₂ := eq19909 X0
       grind)
    | exact superpose eq19909 eq16
    | exact resolve eq16 eq19909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19909
  have eq21012 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq19838 eq20979
    | exact resolve eq20979 eq19838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20979
  have eq21013 : (σ x) = (M.op (M.op x (M.op (σ x) (σ y))) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19838 eq20978
    | exact resolve eq20978 eq19838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19838 eq20978
  have eq21017 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21012 eq21013
    | exact resolve eq21013 eq21012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21012 eq21013
  have eq21175 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21017 eq175
    | exact resolve eq175 eq21017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq21017
  have eq21210 : (σ y) = (M.op (k (σ x) x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19906 eq21175
    | exact resolve eq21175 eq19906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19906 eq21175
  have eq21217 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20898 eq21210
    | exact resolve eq21210 eq20898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20898 eq21210
  have eq21220 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq21217
    | exact resolve eq21217 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq21217
  have eq21221 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq21220
  have eq21222 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq21221 eq27
    | exact resolve eq27 eq21221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq21221
  have eq21242 : False := by grind
  exact eq21242
