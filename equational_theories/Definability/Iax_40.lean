import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation887`: `x = y ◇ ((x ◇ y) ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_x_pxx_pxy_Equation887 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law887 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law887.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X2 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9
    | exact resolve eq9 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X0 (M.op X3 X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 (M.op (M.op X0 X1) (M.op X2 X2)) X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq8 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 (M.op X0 X1)
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq22
    | exact resolve eq22 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 (M.op X1 X1) X1
       have i₂ := eq22 (M.op X0 (M.op X1 X1)) (M.op X1 X1)
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 (M.op X0 X1) X2
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X1) X0 X1
       have i₂ := eq24 (M.op X1 X1) X0
       grind)
    | exact superpose eq24 eq8
    | exact resolve eq8 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) X1
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq38 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X1 X1) X1
       have i₂ := eq26 (M.op X1 X1) X1
       grind)
    | exact superpose eq26 eq11
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq26 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 (M.op X0 X0) X1
       have i₂ := eq26 (M.op (M.op X0 X0) X1) X0
       grind)
    | exact superpose eq26 eq24
    | exact resolve eq24 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq63 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0)
       have i₂ := eq55 X0 (τ X1)
       grind)
    | exact superpose eq55 eq16
    | exact resolve eq16 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq297 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq20
    | exact resolve eq20 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq305 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (M.op X0 X0) X1
       have i₂ := eq55 X0 (σ X1)
       grind)
    | exact superpose eq55 eq20
    | exact resolve eq20 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq55
  have eq324 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq41 x y
       grind)
    | exact superpose eq41 eq14
    | (have j1 := eq41 x x
       grind)
    | exact resolve eq14 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq328 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X0) (σ X1)
       have i₂ := eq41 X0 X1
       grind)
    | exact superpose eq41 eq22
    | (have j1 := eq41 X0 X1
       grind)
    | exact resolve eq22 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq41
  have eq393 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq106 X0 (M.op X1 X1)
       have i₂ := eq26 X0 X1
       grind)
    | exact superpose eq26 eq106
    | (have j0 := eq106 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq106 X0 (M.op X1 X1)
       have r₂ := eq26 X0 X1
       grind)
    | exact resolve eq106 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq398 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq393 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq418 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 (M.op X1 X1)
       have i₂ := eq398 (σ X0) X1
       grind)
    | exact superpose eq398 eq63
    | exact resolve eq63 eq398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq421 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq418 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq418
    | exact resolve eq418 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq2209 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq324
       have i₂ := eq43 x X0 y
       grind)
    | exact superpose eq43 eq324
    | (have j1 := eq43 x X0 x
       grind)
    | exact resolve eq324 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq324
  have eq2213 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x X0) := by
    intro X0
    first
    | (have j0 := eq2209 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2209
  have eq2890 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ (k X0 X1)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq328 (τ X0) (τ X1)
       have i₂ := eq297 X1 X0
       grind)
    | exact superpose eq297 eq328
    | (have j0 := eq328 (τ X0) X1
       grind)
    | exact resolve eq328 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297 eq328
  have eq2992 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X1)) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2890 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq2890
    | (have j0 := eq2890 X0 X1
       grind)
    | exact resolve eq2890 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2890
  have eq3003 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2992 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2992
    | (have j0 := eq2992 X0 X1
       grind)
    | exact resolve eq2992 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2992
  have eq3005 : ∀ X0 X1 : G, (M.op X1 (k X0 X1)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3003 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3003
    | (have j0 := eq3003 X0 X1
       grind)
    | exact resolve eq3003 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3003
  have eq3006 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3005 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3005
    | (have j0 := eq3005 X0 X1
       grind)
    | exact resolve eq3005 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3005
  have eq3348 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X1 ∨ (M.op X2 (k X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X0 X1
       have i₂ := eq3006 X0 X2
       grind)
    | exact superpose eq3006 eq54
    | (have j1 := eq3006 X0 X2
       grind)
    | exact resolve eq54 eq3006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3355 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op X2 (k X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq398 X1 X0
       have i₂ := eq3006 X0 X2
       grind)
    | exact superpose eq3006 eq398
    | (have j1 := eq3006 X0 X2
       grind)
    | exact resolve eq398 eq3006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398 eq3006
  have eq4441 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq3348 X0 x X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3348
  have eq4443 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq4441 X0
       have j1 := eq3355 X0 x X0
       grind)
    | (have r₁ := eq4441 X0
       have r₂ := eq3355 X0 X0 x
       grind)
    | exact resolve eq4441 eq3355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3355 eq4441
  have eq4630 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X0 (k X0 X0) X1 X2
       have i₂ := eq4443 X0
       grind)
    | exact superpose eq4443 eq21
    | exact resolve eq21 eq4443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq4632 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq24 X0 (k X0 X0)
       have i₂ := eq4443 X0
       grind)
    | exact superpose eq4443 eq24
    | exact resolve eq24 eq4443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4443
  have eq4663 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4630 X0 X1 x
       have i₂ := eq27 X0 (M.op X1 X1) x
       grind)
    | exact superpose eq27 eq4630
    | exact resolve eq4630 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq4630
  have eq5898 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq237 X1 (σ (M.op X1 X1))
       have i₂ := eq4663 (σ (M.op X1 X1)) X0
       grind)
    | exact superpose eq4663 eq237
    | exact resolve eq237 eq4663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq5903 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq305 X1 (τ (M.op X1 X1))
       have i₂ := eq4663 (τ (M.op X1 X1)) X0
       grind)
    | exact superpose eq4663 eq305
    | exact resolve eq305 eq4663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305 eq4663
  have eq7818 : ∀ X0 X2 : G, (τ (M.op X0 X0)) = (τ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq5903 x X2
       have i₂ := eq5903 x X0
       grind)
    | exact superpose eq5903 eq5903
    | exact resolve eq5903 eq5903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7897 : ∀ X0 X2 : G, (τ (M.op X0 X0)) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq5898 x X2
       have i₂ := eq5903 x X0
       grind)
    | exact superpose eq5903 eq5898
    | exact resolve eq5898 eq5903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5898
  have eq7902 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 X1
       have i₂ := eq5903 X1 X0
       grind)
    | exact superpose eq5903 eq24
    | exact resolve eq24 eq5903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq11289 : ∀ X0 X1 : G, (M.op (τ (τ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7902 (τ (M.op X0 X0)) X1
       have i₂ := eq7902 X0 (τ (M.op X0 X0))
       grind)
    | exact superpose eq7902 eq7902
    | exact resolve eq7902 eq7902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7902
  have eq13835 : ∀ X0 X1 : G, (k X0 (τ (σ x))) = X0 ∨ x = (k x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq421 X0 (σ x)
       have i₂ := eq2213 X1
       grind)
    | exact superpose eq2213 eq421
    | (have j1 := eq2213 X1
       grind)
    | exact resolve eq421 eq2213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421 eq2213
  have eq13960 : ∀ X0 X1 : G, (k X0 x) = X0 ∨ x = (k x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13835 X0 X1
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq13835
    | (have j0 := eq13835 X0 X1
       grind)
    | exact resolve eq13835 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13835
  have eq19255 : x ≠ x ∨ x = (k x x) := by
    first
    | (have j0 := eq13960 x x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13960
  have eq19256 : x = (k x x) := by grind
  clear eq19255
  have eq19262 : x = (M.op x x) := by
    first
    | (have i₁ := eq19256
       have i₂ := eq4632 x
       grind)
    | exact superpose eq4632 eq19256
    | exact resolve eq19256 eq4632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4632 eq19256
  have eq19553 : ∀ X0 : G, (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq26 X0 x
       have i₂ := eq19262
       grind)
    | exact superpose eq19262 eq26
    | exact resolve eq26 eq19262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq19556 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq32 X0 x
       have i₂ := eq19262
       grind)
    | exact superpose eq19262 eq32
    | exact resolve eq32 eq19262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq19557 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq54 x X0
       have i₂ := eq19262
       grind)
    | exact superpose eq19262 eq54
    | exact resolve eq54 eq19262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq19575 : ∀ X0 : G, (M.op X0 X0) = (τ x) := by
    intro X0
    first
    | (have i₁ := eq5903 X0 x
       have i₂ := eq19262
       grind)
    | exact superpose eq19262 eq5903
    | exact resolve eq5903 eq19262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5903
  have eq19585 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ x) := by
    intro X0
    first
    | (have i₁ := eq7818 x X0
       have i₂ := eq19262
       grind)
    | exact superpose eq19262 eq7818
    | exact resolve eq7818 eq19262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7818 eq19262
  have eq20045 : ∀ X0 : G, x = (τ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11289 X0 x
       have i₂ := eq19553 (τ (τ (M.op X0 X0)))
       grind)
    | exact superpose eq19553 eq11289
    | exact resolve eq11289 eq19553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11289 eq19553
  have eq20048 : x = (τ (τ x)) := by
    first
    | (have i₁ := eq20045 x
       have i₂ := eq19585 x
       grind)
    | exact superpose eq19585 eq20045
    | exact resolve eq20045 eq19585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19585 eq20045
  have eq20565 : ∀ X0 : G, (σ x) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7897 X0 x
       have i₂ := eq19556 x
       grind)
    | exact superpose eq19556 eq7897
    | exact resolve eq7897 eq19556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7897 eq19556
  have eq20710 : (σ x) = (τ (τ x)) := by
    first
    | (have i₁ := eq20565 x
       have i₂ := eq19575 x
       grind)
    | exact superpose eq19575 eq20565
    | exact resolve eq20565 eq19575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19575 eq20565
  have eq20749 : x = (σ x) := by
    first
    | (have i₁ := eq20710
       have i₂ := eq20048
       grind)
    | exact superpose eq20048 eq20710
    | exact resolve eq20710 eq20048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20048 eq20710
  have eq21167 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq20749
       grind)
    | exact superpose eq20749 eq14
    | exact resolve eq14 eq20749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20749
  have eq21234 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq21167
       have i₂ := eq19557 (σ y)
       grind)
    | exact superpose eq19557 eq21167
    | exact resolve eq21167 eq19557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21167
  have eq21253 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq21234
       have i₂ := eq19557 y
       grind)
    | exact superpose eq19557 eq21234
    | exact resolve eq21234 eq19557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19557 eq21234
  have eq21254 : False := by grind
  exact eq21254

/-- `Equation887`: `x = y ◇ ((x ◇ y) ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation887 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law887 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law887.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X2 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X0 (M.op X3 X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 (M.op (M.op X0 X1) (M.op X2 X2)) X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq8 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 (M.op X0 X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 (M.op X1 X1) X1
       have i₂ := eq19 (M.op X0 (M.op X1 X1)) (M.op X1 X1)
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 (M.op X0 X1) X2
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq34 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X1) X0 X1
       have i₂ := eq21 (M.op X1 X1) X0
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq58 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 (M.op X0 X0) X1
       have i₂ := eq23 (M.op (M.op X0 X0) X1) X0
       grind)
    | exact superpose eq23 eq21
    | exact resolve eq21 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq104 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq30 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq297 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq46
    | exact resolve eq46 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq370 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq104 (M.op X1 X1) X0
       have i₂ := eq58 X1 X0
       grind)
    | exact superpose eq58 eq104
    | (have j0 := eq104 (M.op X1 X1) X0
       grind)
    | (have r₁ := eq104 (M.op X0 X0) X1
       have r₂ := eq58 X0 X1
       grind)
    | exact resolve eq104 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq104
  have eq372 : ∀ X0 X1 : G, (k (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq370 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq403 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq34 x y
       grind)
    | exact superpose eq34 eq14
    | (have j1 := eq34 x y
       grind)
    | exact resolve eq14 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq419 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ X0) (σ X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq19
    | (have j1 := eq34 X0 X1
       grind)
    | exact resolve eq19 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq446 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq34 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq492 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq46 (M.op X1 X1) X0
       have i₂ := eq372 (σ X0) X1
       grind)
    | exact superpose eq372 eq46
    | exact resolve eq46 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq493 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op X1 X1)
       have i₂ := eq372 (τ X0) X1
       grind)
    | exact superpose eq372 eq17
    | exact resolve eq17 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq494 : ∀ X0 X1 : G, (k (σ (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq493 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq493
    | exact resolve eq493 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq495 : ∀ X0 X1 : G, (k (τ (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq492 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq492
    | exact resolve eq492 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq1170 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq446 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq446
    | (have j0 := eq446 (τ X0)
       grind)
    | exact resolve eq446 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq446
  have eq1180 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1170 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1170
    | (have j0 := eq1170 X0
       grind)
    | exact resolve eq1170 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170
  have eq1185 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1180 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1180
    | (have j0 := eq1180 X0
       grind)
    | exact resolve eq1180 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180
  have eq2364 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq403
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq403
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq403 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq2375 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq2364
  have eq3120 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ (k X0 X1)))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq419 (τ X0) (τ X1)
       have i₂ := eq297 X1 X0
       grind)
    | exact superpose eq297 eq419
    | (have j0 := eq419 (τ X0) (τ X1)
       grind)
    | exact resolve eq419 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297 eq419
  have eq3311 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X1)) (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3120 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq3120
    | (have j0 := eq3120 X0 X1
       grind)
    | exact resolve eq3120 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3120
  have eq3338 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 (k X0 X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3311 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3311
    | (have j0 := eq3311 X0 X1
       grind)
    | exact resolve eq3311 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3311
  have eq3344 : ∀ X0 X1 : G, (M.op X1 (k X0 X1)) = X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3338 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3338
    | (have j0 := eq3338 X0 X1
       grind)
    | exact resolve eq3338 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3338
  have eq3349 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (M.op X1 (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3344 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3344
    | (have j0 := eq3344 X0 X1
       grind)
    | exact resolve eq3344 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3344
  have eq3350 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3349 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3349
    | (have j0 := eq3349 X0 X1
       grind)
    | exact resolve eq3349 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3349
  have eq3713 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (M.op X0 (k X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X1 X2
       have i₂ := eq3350 X2 X0
       grind)
    | (have i₁ := eq23 X0 X1
       have i₂ := eq3350 X0 (M.op X1 X1)
       grind)
    | exact superpose eq3350 eq23
    | (have j1 := eq3350 X2 X0
       grind)
    | exact resolve eq23 eq3350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3723 : ∀ X0 X1 X2 : G, (k X2 X0) = X0 ∨ (M.op X0 (k X1 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq91 X0 X1
       have i₂ := eq3350 X0 X1
       grind)
    | (have i₁ := eq91 X0 X1
       have i₂ := eq3350 X0 (M.op X0 X0)
       grind)
    | exact superpose eq3350 eq91
    | (have j1 := eq3350 X1 X0
       grind)
    | exact resolve eq91 eq3350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq3350
  have eq4679 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) X0) = X1 ∨ (M.op X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X1 (k X0 X1)
       have i₂ := eq3713 X1 X2 X0
       grind)
    | exact superpose eq3713 eq19
    | (have j1 := eq3713 X1 X2 X2
       grind)
    | exact resolve eq19 eq3713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3713
  have eq5729 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) X0) = X1 ∨ (k X2 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X1 (k X0 X1)
       have i₂ := eq3723 X1 X0 X2
       grind)
    | exact superpose eq3723 eq19
    | (have j1 := eq3723 X1 X1 X2
       grind)
    | exact resolve eq19 eq3723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq3723
  have eq7684 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq4679 X0 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4679
  have eq7685 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7684 X0
       have j1 := eq5729 X0 X0 x
       grind)
    | (have r₁ := eq7684 x
       have r₂ := eq5729 X0 x x
       grind)
    | exact resolve eq7684 eq5729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5729 eq7684
  have eq8009 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq21 (k X0 X0) X0
       have i₂ := eq7685 X0
       grind)
    | exact superpose eq7685 eq21
    | exact resolve eq21 eq7685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7685
  have eq8848 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (k X0 X0) X1 X2
       have i₂ := eq8009 X0
       grind)
    | exact superpose eq8009 eq18
    | exact resolve eq18 eq8009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq8895 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8848 X0 X1 x
       have i₂ := eq24 X0 (M.op X1 X1) x
       grind)
    | exact superpose eq24 eq8848
    | exact resolve eq8848 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq8848
  have eq9771 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1185 X1
       have i₂ := eq8895 X1 X0
       grind)
    | exact superpose eq8895 eq1185
    | (have j0 := eq1185 X1
       grind)
    | (have r₁ := eq1185 (M.op X1 X1)
       have r₂ := eq8895 (M.op X1 X1) X1
       grind)
    | exact resolve eq1185 eq8895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185
  have eq9825 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq494 (σ (M.op X1 X1)) X1
       have i₂ := eq8895 (σ (M.op X1 X1)) X0
       grind)
    | exact superpose eq8895 eq494
    | exact resolve eq494 eq8895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494
  have eq9832 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq495 (τ (M.op X1 X1)) X1
       have i₂ := eq8895 (τ (M.op X1 X1)) X0
       grind)
    | exact superpose eq8895 eq495
    | exact resolve eq495 eq8895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8895
  have eq12480 : ∀ X0 X2 : G, (τ (M.op X0 X0)) = (τ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq9832 x X2
       have i₂ := eq9832 x X0
       grind)
    | exact superpose eq9832 eq9832
    | exact resolve eq9832 eq9832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12577 : ∀ X0 X2 : G, (τ (M.op X0 X0)) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq9825 x X2
       have i₂ := eq9832 x X0
       grind)
    | exact superpose eq9832 eq9825
    | exact resolve eq9825 eq9832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9825
  have eq12582 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 X1
       have i₂ := eq9832 X1 X0
       grind)
    | exact superpose eq9832 eq21
    | exact resolve eq21 eq9832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq18918 : ∀ X0 X1 : G, (M.op (τ (τ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12582 (τ (M.op X0 X0)) X1
       have i₂ := eq12582 X0 (τ (M.op X0 X0))
       grind)
    | exact superpose eq12582 eq12582
    | exact resolve eq12582 eq12582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12582
  have eq27584 : ∀ X0 : G, (k (τ (σ y)) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq495 X0 (σ x)
       have i₂ := eq2375
       grind)
    | exact superpose eq2375 eq495
    | exact resolve eq495 eq2375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495 eq2375
  have eq27665 : ∀ X0 : G, (k y X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq27584 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq27584
    | exact resolve eq27584 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27584
  have eq32502 : y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8009 y
       have i₂ := eq27665 y
       grind)
    | exact superpose eq27665 eq8009
    | exact resolve eq8009 eq27665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8009 eq27665
  have eq32571 : y = (M.op y y) := by
    first
    | (have j1 := eq9771 x y
       grind)
    | (have r₁ := eq32502
       have r₂ := eq9771 y y
       grind)
    | (have r₁ := eq32502
       have r₂ := eq9771 x y
       grind)
    | exact resolve eq32502 eq9771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9771 eq32502
  have eq32588 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 X0 y
       have i₂ := eq32571
       grind)
    | exact superpose eq32571 eq23
    | exact resolve eq23 eq32571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq32592 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq39 X0 y
       have i₂ := eq32571
       grind)
    | exact superpose eq32571 eq39
    | exact resolve eq39 eq32571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq32613 : ∀ X0 : G, (M.op X0 X0) = (τ y) := by
    intro X0
    first
    | (have i₁ := eq9832 X0 y
       have i₂ := eq32571
       grind)
    | exact superpose eq32571 eq9832
    | exact resolve eq9832 eq32571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9832
  have eq32624 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ y) := by
    intro X0
    first
    | (have i₁ := eq12480 y X0
       have i₂ := eq32571
       grind)
    | exact superpose eq32571 eq12480
    | exact resolve eq12480 eq32571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12480 eq32571
  have eq33072 : ∀ X0 : G, y = (τ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq18918 X0 y
       have i₂ := eq32588 (τ (τ (M.op X0 X0)))
       grind)
    | exact superpose eq32588 eq18918
    | exact resolve eq18918 eq32588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18918
  have eq33077 : y = (τ (τ y)) := by
    first
    | (have i₁ := eq33072 x
       have i₂ := eq32624 x
       grind)
    | exact superpose eq32624 eq33072
    | exact resolve eq33072 eq32624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32624 eq33072
  have eq33937 : ∀ X0 : G, (σ y) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12577 X0 x
       have i₂ := eq32592 x
       grind)
    | exact superpose eq32592 eq12577
    | exact resolve eq12577 eq32592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12577 eq32592
  have eq34116 : (σ y) = (τ (τ y)) := by
    first
    | (have i₁ := eq33937 x
       have i₂ := eq32613 x
       grind)
    | exact superpose eq32613 eq33937
    | exact resolve eq33937 eq32613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32613 eq33937
  have eq34172 : y = (σ y) := by
    first
    | (have i₁ := eq34116
       have i₂ := eq33077
       grind)
    | exact superpose eq33077 eq34116
    | exact resolve eq34116 eq33077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33077 eq34116
  have eq34709 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq34172
       grind)
    | exact superpose eq34172 eq14
    | exact resolve eq14 eq34172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34172
  have eq34816 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq34709
       have i₂ := eq32588 (σ x)
       grind)
    | exact superpose eq32588 eq34709
    | exact resolve eq34709 eq32588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34709
  have eq34845 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq34816
       have i₂ := eq32588 x
       grind)
    | exact superpose eq32588 eq34816
    | exact resolve eq34816 eq32588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32588 eq34816
  have eq34846 : False := by grind
  exact eq34846

/-- `Equation895`: `x = y ◇ ((x ◇ z) ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_x_pxx_pxy_Equation895 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law895 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law895.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X2) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9
    | exact resolve eq9 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X0 X3) (M.op X2 X3))))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X1 (M.op (M.op X0 X3) (M.op X2 X3))
       have i₂ := eq8 X0 X2 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) X1
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq42 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq78 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X0 X1 X1 x
       have i₂ := eq8 X0 X1 x
       grind)
    | exact superpose eq8 eq21
    | exact resolve eq21 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq102 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 (M.op X1 X1)
       have i₂ := eq91 X1 X0
       grind)
    | exact superpose eq91 eq78
    | (have j0 := eq78 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq78 X1 (M.op X0 X0)
       have r₂ := eq91 X0 X1
       grind)
    | exact resolve eq78 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq105 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0) X1
       have i₂ := eq91 X0 (M.op X0 X0)
       grind)
    | exact superpose eq91 eq11
    | (have r₁ := eq11 (M.op X0 X0) X1
       have r₂ := eq91 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 X1
       have i₂ := eq91 X1 (M.op X0 X1)
       grind)
    | exact superpose eq91 eq8
    | exact resolve eq8 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq105 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq109 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq102 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq144 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq107 X1 (M.op X0 X1)
       have i₂ := eq107 X0 X1
       grind)
    | exact superpose eq107 eq107
    | exact resolve eq107 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq107 X0 (M.op X1 X1)
       have i₂ := eq91 X1 X0
       grind)
    | exact superpose eq91 eq107
    | exact resolve eq107 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq202 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (M.op X1 X1)
       have i₂ := eq109 (σ X0) X1
       grind)
    | exact superpose eq109 eq28
    | exact resolve eq28 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq109
  have eq208 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq202 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq202
    | exact resolve eq202 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq264 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq144 X0 (M.op X1 X1)
       have i₂ := eq91 X1 X0
       grind)
    | exact superpose eq91 eq144
    | exact resolve eq144 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq144
  have eq444 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq44 x y
       grind)
    | exact superpose eq44 eq14
    | (have j1 := eq44 x x
       grind)
    | exact resolve eq14 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq480 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq44 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq1227 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (M.op X0 X0) X1
       have i₂ := eq108 X0 (σ X1)
       grind)
    | exact superpose eq108 eq20
    | exact resolve eq20 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq108
  have eq2485 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq480 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq480
    | (have j0 := eq480 (τ X0)
       grind)
    | exact resolve eq480 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq480
  have eq2496 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2485 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2485
    | (have j0 := eq2485 X0
       grind)
    | exact resolve eq2485 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2485
  have eq2505 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2496 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2496
    | (have j0 := eq2496 X0
       grind)
    | exact resolve eq2496 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2496
  have eq6147 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq444
       have i₂ := eq48 x X0 y
       grind)
    | exact superpose eq48 eq444
    | (have j1 := eq48 x X0 x
       grind)
    | exact resolve eq444 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq444
  have eq6154 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x X0) := by
    intro X0
    first
    | (have j0 := eq6147 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6147
  have eq170059 : ∀ X0 X1 : G, (τ (σ x)) = (k (τ (σ x)) X0) ∨ x = (k x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1227 (σ x) X1
       have i₂ := eq6154 X0
       grind)
    | exact superpose eq6154 eq1227
    | (have j1 := eq6154 X1
       grind)
    | exact resolve eq1227 eq6154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227 eq6154
  have eq170369 : ∀ X0 X1 : G, x = (k x X0) ∨ x = (k x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq170059 X0 X1
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq170059
    | (have j0 := eq170059 X0 X0
       grind)
    | exact resolve eq170059 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170059
  have eq175942 : ∀ X0 : G, x ≠ x ∨ x = (k x X0) := by
    intro X0
    first
    | (have j0 := eq170369 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170369
  have eq175943 : ∀ X0 : G, x = (k x X0) := by
    intro X0
    first
    | (have j0 := eq175942 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175942
  have eq185729 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2505 x
       have i₂ := eq175943 x
       grind)
    | exact superpose eq175943 eq2505
    | (have j0 := eq2505 x
       grind)
    | (have r₁ := eq2505 x
       have r₂ := eq175943 x
       grind)
    | exact resolve eq2505 eq175943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175943
  have eq185777 : x = (M.op x x) := by grind
  clear eq185729
  have eq186056 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq145 X0 x
       have i₂ := eq185777
       grind)
    | exact superpose eq185777 eq145
    | exact resolve eq145 eq185777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq186058 : ∀ X0 : G, (k X0 (τ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq208 X0 x
       have i₂ := eq185777
       grind)
    | exact superpose eq185777 eq208
    | exact resolve eq208 eq185777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq186060 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq264 X0 x
       have i₂ := eq185777
       grind)
    | exact superpose eq185777 eq264
    | exact resolve eq264 eq185777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq185777
  have eq199913 : (τ x) ≠ (τ x) ∨ (τ x) = (M.op (τ x) (τ x)) := by
    first
    | (have i₁ := eq2505 (τ x)
       have i₂ := eq186058 (τ x)
       grind)
    | exact superpose eq186058 eq2505
    | (have j0 := eq2505 (τ x)
       grind)
    | (have r₁ := eq2505 (τ x)
       have r₂ := eq186058 (τ x)
       grind)
    | exact resolve eq2505 eq186058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2505 eq186058
  have eq199966 : (τ x) = (M.op (τ x) (τ x)) := by grind
  clear eq199913
  have eq200008 : x = (τ x) := by
    first
    | (have i₁ := eq199966
       have i₂ := eq186060 (τ x)
       grind)
    | exact superpose eq186060 eq199966
    | exact resolve eq199966 eq186060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186060 eq199966
  have eq201638 : x = (σ x) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq200008
       grind)
    | exact superpose eq200008 eq10
    | exact resolve eq10 eq200008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200008
  have eq202369 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq201638
       grind)
    | exact superpose eq201638 eq14
    | exact resolve eq14 eq201638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201638
  have eq202439 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq202369
       have i₂ := eq186056 (σ y)
       grind)
    | exact superpose eq186056 eq202369
    | exact resolve eq202369 eq186056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202369
  have eq202463 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq202439
       have i₂ := eq186056 y
       grind)
    | exact superpose eq186056 eq202439
    | exact resolve eq202439 eq186056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186056 eq202439
  have eq202464 : False := by grind
  exact eq202464

/-- `Equation895`: `x = y ◇ ((x ◇ z) ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation895 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law895 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law895.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X2) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X0 X3) (M.op X2 X3))))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X1 (M.op (M.op X0 X3) (M.op X2 X3))
       have i₂ := eq8 X0 X2 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq27 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq29 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 X2))) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 X1 X2
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X0 X2)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq27 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 X1 x
       have i₂ := eq8 X0 X1 x
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq82 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 X1
       have i₂ := eq66 X1 (M.op X0 X1)
       grind)
    | exact superpose eq66 eq8
    | exact resolve eq8 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq82 X1 (M.op X0 X1)
       have i₂ := eq82 X0 X1
       grind)
    | exact superpose eq82 eq82
    | exact resolve eq82 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 (M.op X1 X1)
       have i₂ := eq66 X1 X0
       grind)
    | exact superpose eq66 eq82
    | exact resolve eq82 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq173 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq114 X0 (M.op X1 X1)
       have i₂ := eq66 X1 X0
       grind)
    | exact superpose eq66 eq114
    | exact resolve eq114 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op (M.op X0 X1) X0) ∨ (k (M.op X2 X1) X2) = (M.op (M.op X2 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 X2 (M.op X0 X1) (M.op X2 X1)
       have i₂ := eq8 X0 X2 X1
       grind)
    | exact superpose eq8 eq29
    | (have j0 := eq29 X2 X1 (M.op X2 X1)
       grind)
    | exact resolve eq29 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq250 : ∀ X1 X2 : G, (M.op X2 X1) = X1 ∨ (k (M.op X2 X1) X2) = (M.op (M.op X2 X1) X2) := by
    intro X1 X2
    first
    | (have i₁ := eq209 x X1 X2
       have i₂ := eq114 x X1
       grind)
    | exact superpose eq114 eq209
    | (have j0 := eq209 x X1 X2
       grind)
    | exact resolve eq209 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq262 : ∀ X1 X2 : G, (k (M.op X2 X1) X2) = X1 ∨ (M.op X2 X1) = X1 := by
    intro X1 X2
    first
    | (have i₁ := eq250 X1 X2
       have i₂ := eq114 X2 X1
       grind)
    | exact superpose eq114 eq250
    | (have j0 := eq250 X1 X2
       grind)
    | exact resolve eq250 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq288 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 X1
       have i₂ := eq115 (M.op X0 X1) X1
       grind)
    | exact superpose eq115 eq8
    | exact resolve eq8 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq498 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq114 X1 (M.op X1 X0)
       have i₂ := eq288 X1 X0
       grind)
    | exact superpose eq288 eq114
    | exact resolve eq114 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq288
  have eq541 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq31 x y
       grind)
    | exact superpose eq31 eq14
    | (have j1 := eq31 x y
       grind)
    | exact resolve eq14 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq810 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq47 (M.op X1 X1) X0
       have i₂ := eq115 X0 X1
       grind)
    | exact superpose eq115 eq47
    | (have j0 := eq47 (M.op X1 X1) X0
       grind)
    | (have r₁ := eq47 (M.op X1 X1) X0
       have r₂ := eq115 X0 X1
       grind)
    | exact resolve eq47 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq814 : ∀ X0 X1 : G, (k (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq810 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810
  have eq841 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (M.op X1 X1) X0
       have i₂ := eq814 (σ X0) X1
       grind)
    | exact superpose eq814 eq24
    | exact resolve eq24 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq842 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op X1 X1)
       have i₂ := eq814 (τ X0) X1
       grind)
    | exact superpose eq814 eq17
    | exact resolve eq17 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq843 : ∀ X0 X1 : G, (k (σ (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq842 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq842
    | exact resolve eq842 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq844 : ∀ X0 X1 : G, (k (τ (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq841 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq841
    | exact resolve eq841 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841
  have eq846 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq262 (M.op X0 X0) X1
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq262
    | exact resolve eq262 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq900 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (σ (M.op X1 X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (M.op X1 X1))
       have i₂ := eq843 (τ X0) X1
       grind)
    | exact superpose eq843 eq17
    | exact resolve eq17 eq843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq901 : ∀ X0 X1 : G, (k (σ (σ (M.op X1 X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq900 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq900
    | exact resolve eq900 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq1103 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (τ (M.op X1 X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (τ (M.op X1 X1)) X0
       have i₂ := eq844 (σ X0) X1
       grind)
    | exact superpose eq844 eq24
    | exact resolve eq24 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq1106 : ∀ X0 X1 : G, (k (τ (τ (M.op X1 X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1103 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1103
    | exact resolve eq1103 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103
  have eq1234 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (σ (σ (M.op X1 X1)))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (M.op X1 X1)))
       have i₂ := eq901 (τ X0) X1
       grind)
    | exact superpose eq901 eq17
    | exact resolve eq17 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq1235 : ∀ X0 X1 : G, (k (σ (σ (σ (M.op X1 X1)))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1234 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1234
    | exact resolve eq1234 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1234
  have eq2942 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq541
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq541
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq541 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq2943 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq2942
  have eq103855 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq843 (σ (M.op X1 X1)) X1
       have i₂ := eq846 (σ (M.op X1 X1)) X0
       grind)
    | exact superpose eq846 eq843
    | (have j1 := eq846 (σ (M.op X1 X1)) X0
       grind)
    | exact resolve eq843 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq103856 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (M.op X1 X1))) ∨ (M.op X0 X0) = (σ (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq901 (σ (σ (M.op X1 X1))) X1
       have i₂ := eq846 (σ (σ (M.op X1 X1))) X0
       grind)
    | exact superpose eq846 eq901
    | (have j1 := eq846 (σ (σ (M.op X1 X1))) X0
       grind)
    | exact resolve eq901 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901
  have eq103857 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (σ (M.op X1 X1)))) ∨ (M.op X0 X0) = (σ (σ (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1235 (σ (σ (σ (M.op X1 X1)))) X1
       have i₂ := eq846 (σ (σ (σ (M.op X1 X1)))) X0
       grind)
    | exact superpose eq846 eq1235
    | (have j1 := eq846 (σ (σ (σ (M.op X1 X1)))) X0
       grind)
    | exact resolve eq1235 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1235
  have eq103862 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq844 (τ (M.op X1 X1)) X1
       have i₂ := eq846 (τ (M.op X1 X1)) X0
       grind)
    | exact superpose eq846 eq844
    | (have j1 := eq846 (τ (M.op X1 X1)) X0
       grind)
    | exact resolve eq844 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq103863 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (τ (M.op X1 X1))) ∨ (M.op X0 X0) = (τ (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1106 (τ (τ (M.op X1 X1))) X1
       have i₂ := eq846 (τ (τ (M.op X1 X1))) X0
       grind)
    | exact superpose eq846 eq1106
    | (have j1 := eq846 (τ (τ (M.op X1 X1))) X0
       grind)
    | exact resolve eq1106 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106
  have eq103866 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq846 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq103869 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq103863 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103863
  have eq103870 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq103862 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103862
  have eq103872 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have j0 := eq103857 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103857
  have eq103873 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq103856 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103856
  have eq103874 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq103855 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103855
  have eq108069 : ∀ X0 X2 : G, (σ (M.op X0 X0)) = (τ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq103870 x X2
       have i₂ := eq103874 x X0
       grind)
    | exact superpose eq103874 eq103870
    | exact resolve eq103870 eq103874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119818 : ∀ X0 X2 : G, (τ (M.op X2 X2)) = (σ (σ (σ (M.op X0 X0)))) := by
    intro X0 X2
    first
    | (have i₁ := eq108069 x X2
       have i₂ := eq103873 x X0
       grind)
    | exact superpose eq103873 eq108069
    | exact resolve eq108069 eq103873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103873 eq108069
  have eq125263 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq103866 X1 X0
       have i₂ := eq27 X0 X0
       grind)
    | exact superpose eq27 eq103866
    | (have j0 := eq103866 X1 X0
       have j1 := eq27 X0 X0
       grind)
    | (have r₁ := eq103866 X0 X0
       have r₂ := eq27 X0 X0
       grind)
    | exact resolve eq103866 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq125285 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq125263 X0 X1
       have j1 := eq103866 X1 X0
       grind)
    | (have r₁ := eq125263 X1 X1
       have r₂ := eq103866 X1 X1
       grind)
    | (have r₁ := eq125263 (M.op X0 X0) X1
       have r₂ := eq103866 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | (have r₁ := eq125263 (k (M.op X1 X1) (M.op X1 X1)) X1
       have r₂ := eq103866 X0 (M.op X1 X1)
       grind)
    | exact resolve eq125263 eq103866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103866 eq125263
  have eq125646 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq125285 X1 X2
       have i₂ := eq173 X1 X0
       grind)
    | (have i₁ := eq125285 X1 X2
       have i₂ := eq173 X0 X1
       grind)
    | exact superpose eq173 eq125285
    | (have j0 := eq125285 X1 X2
       grind)
    | (have r₁ := eq125285 (M.op X1 X1) X1
       have r₂ := eq173 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq125285 (M.op X0 X0) X1
       have r₂ := eq173 X0 (M.op X0 X0)
       grind)
    | exact resolve eq125285 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173 eq125285
  have eq128311 : ∀ X0 X2 X3 : G, (σ (σ (σ (M.op X0 X0)))) ≠ X2 ∨ (M.op X3 X3) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq125646 x X2 X3
       have i₂ := eq103872 x X0
       grind)
    | exact superpose eq103872 eq125646
    | (have j0 := eq125646 X0 X2 X3
       grind)
    | (have r₁ := eq125646 X0 (σ (σ (σ (M.op x x)))) X2
       have r₂ := eq103872 X0 x
       grind)
    | exact resolve eq125646 eq103872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103872 eq125646
  have eq147851 : ∀ X0 : G, (σ (σ (σ (M.op X0 X0)))) = (τ (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq119818 X0 (σ x)
       have i₂ := eq2943
       grind)
    | exact superpose eq2943 eq119818
    | exact resolve eq119818 eq2943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2943 eq119818
  have eq147954 : ∀ X0 : G, y = (σ (σ (σ (M.op X0 X0)))) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq147851 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq147851
    | exact resolve eq147851 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147851
  have eq147995 : y = (M.op x x) := by
    first
    | (have j1 := eq128311 x y x
       grind)
    | (have r₁ := eq147954 x
       have r₂ := eq128311 x y x
       grind)
    | exact resolve eq147954 eq128311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128311 eq147954
  have eq148007 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq66 x X0
       have i₂ := eq147995
       grind)
    | exact superpose eq147995 eq66
    | exact resolve eq66 eq147995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq148009 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq115 X0 x
       have i₂ := eq147995
       grind)
    | exact superpose eq147995 eq115
    | exact resolve eq115 eq147995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq148027 : ∀ X0 : G, (M.op X0 X0) = (τ (τ y)) := by
    intro X0
    first
    | (have i₁ := eq103869 X0 x
       have i₂ := eq147995
       grind)
    | exact superpose eq147995 eq103869
    | exact resolve eq103869 eq147995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103869
  have eq148028 : ∀ X0 : G, (M.op X0 X0) = (τ y) := by
    intro X0
    first
    | (have i₁ := eq103870 X0 x
       have i₂ := eq147995
       grind)
    | exact superpose eq147995 eq103870
    | exact resolve eq103870 eq147995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103870
  have eq148032 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq103874 X0 x
       have i₂ := eq147995
       grind)
    | exact superpose eq147995 eq103874
    | exact resolve eq103874 eq147995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103874 eq147995
  have eq148240 : (σ y) = (τ y) := by
    first
    | (have i₁ := eq148028 x
       have i₂ := eq148032 x
       grind)
    | exact superpose eq148032 eq148028
    | exact resolve eq148028 eq148032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148028
  have eq148241 : (σ y) = (τ (τ y)) := by
    first
    | (have i₁ := eq148027 x
       have i₂ := eq148032 x
       grind)
    | exact superpose eq148032 eq148027
    | exact resolve eq148027 eq148032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148027 eq148032
  have eq148289 : (σ y) = (τ (σ y)) := by
    first
    | (have i₁ := eq148241
       have i₂ := eq148240
       grind)
    | exact superpose eq148240 eq148241
    | exact resolve eq148241 eq148240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148240 eq148241
  have eq148321 : y = (σ y) := by
    first
    | (have i₁ := eq148289
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq148289
    | exact resolve eq148289 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148289
  have eq148502 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq148321
       grind)
    | exact superpose eq148321 eq14
    | exact resolve eq14 eq148321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148321
  have eq148546 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
    first
    | (have i₁ := eq148502
       have i₂ := eq498 (σ x) y
       grind)
    | (have i₁ := eq148502
       have i₂ := eq498 y (σ x)
       grind)
    | exact superpose eq498 eq148502
    | exact resolve eq148502 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498 eq148502
  have eq148561 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq148546
       have i₂ := eq148009 (σ x)
       grind)
    | exact superpose eq148009 eq148546
    | exact resolve eq148546 eq148009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148009 eq148546
  have eq148568 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq148561
       have i₂ := eq148007 x
       grind)
    | exact superpose eq148007 eq148561
    | exact resolve eq148561 eq148007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148007 eq148561
  have eq148569 : False := by grind
  exact eq148569

/-- `Equation898`: `x = y ◇ ((x ◇ z) ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation898 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law898 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law898.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq127 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq131 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq127 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq127 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq127 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq127 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq150 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq131 (σ X0) (σ X1)
       grind)
    | exact superpose eq131 eq13
    | exact resolve eq13 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq150 X0 X1
       have i₂ := eq131 X0 X1
       grind)
    | exact superpose eq131 eq150
    | exact resolve eq150 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq150
  have eq763 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq159 x y
       grind)
    | exact superpose eq159 eq14
    | (have r₁ := eq14
       have r₂ := eq159 x y
       grind)
    | exact resolve eq14 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq789 : False := by grind
  exact eq789

/-- `Equation907`: `x = y ◇ ((y ◇ x) ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation907 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law907 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law907.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq93 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq97 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq93 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq93 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq93 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq93 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq113 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq97 (σ X0) (σ X1)
       grind)
    | exact superpose eq97 eq13
    | exact resolve eq13 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq113 X0 X1
       have i₂ := eq97 X0 X1
       grind)
    | exact superpose eq97 eq113
    | exact resolve eq113 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq113
  have eq1105 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq120 x y
       grind)
    | exact superpose eq120 eq14
    | (have r₁ := eq14
       have r₂ := eq120 x y
       grind)
    | exact resolve eq14 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq1132 : False := by grind
  exact eq1132

/-- `Equation916`: `x = y ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_x_pxy_Equation916 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law916 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law916.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9
    | exact resolve eq9 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq21 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have i₂ := eq8 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X1 (M.op (M.op X1 X1) (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op (M.op X1 X1) (M.op X0 X0))
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq11
    | (have j0 := eq11 X1 (M.op (M.op X1 X1) (M.op X0 X0))
       grind)
    | (have r₁ := eq11 X1 (M.op (M.op X1 X1) (M.op (M.op X1 X1) (M.op X1 X1)))
       have r₂ := eq8 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X2 X2) (M.op X0 X1))) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X2
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X1 X1
       have i₂ := eq12 X1 X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X1)) = X0 ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X0
       have i₂ := eq12 (M.op X0 X0) X1
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 (M.op X1 X1) (M.op X0 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 (M.op X0 X0) X1
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq53 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq20
    | exact resolve eq20 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq50
    | exact resolve eq50 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq50 X0 (τ X1)
       grind)
    | exact superpose eq50 eq16
    | (have j1 := eq50 X0 (τ X1)
       grind)
    | exact resolve eq16 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq70 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq89 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq21 (M.op X0 X0)
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq21
    | exact resolve eq21 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 X0 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X1) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X0 X0) X1
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X0)
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 : G, (k X0 (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))) = X0 := by
    intro X0
    first
    | (have j0 := eq30 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq104 : ∀ X0 : G, (k X0 (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq103 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq103
    | exact resolve eq103 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq105 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 (M.op (M.op X1 X1) (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq70 X1 (M.op (M.op X1 X1) (M.op X0 X0))
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq70
    | (have j0 := eq70 X1 (M.op (M.op X1 X1) (M.op X0 X0))
       grind)
    | (have r₁ := eq70 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq8 X0 X0
       grind)
    | exact resolve eq70 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq70 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq70
    | (have j0 := eq70 X0 (M.op X0 (M.op X0 X0))
       grind)
    | (have r₁ := eq70 X0 (M.op X0 (M.op X0 X0))
       have r₂ := eq91 X0
       grind)
    | exact resolve eq70 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (k X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq106 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq138 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (M.op (σ X0) (σ X0))))) := by
    intro X0
    first
    | (have i₁ := eq27 X0 (M.op (σ X0) (M.op (σ X0) (σ X0)))
       have i₂ := eq110 (σ X0)
       grind)
    | exact superpose eq110 eq27
    | exact resolve eq27 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq110
  have eq142 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (M.op (σ X0) (σ X0))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq138 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq138
    | exact resolve eq138 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq496 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq701 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq94 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have i₂ := eq8 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)
       grind)
    | exact superpose eq8 eq94
    | exact resolve eq94 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq720 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 X1) (M.op X0 X0))) = X2 ∨ (M.op X0 X0) = (k X2 (M.op (M.op X2 X2) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41 X1 (M.op (M.op X1 X1) (M.op X0 (M.op X0 X0))) X2
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq41
    | exact resolve eq41 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq727 : ∀ X0 X2 : G, (M.op X0 X0) = (k X2 (M.op (M.op X2 X2) (M.op X0 (M.op X0 X0)))) ∨ X0 = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq720 X0 x X2
       have i₂ := eq8 X0 x
       grind)
    | exact superpose eq8 eq720
    | (have j0 := eq720 X0 x X2
       grind)
    | exact resolve eq720 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq733 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq701 X0
       have i₂ := eq8 X0 X0
       grind)
    | exact superpose eq8 eq701
    | exact resolve eq701 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq739 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq733 X0
       have i₂ := eq21 (M.op X0 X0)
       grind)
    | exact superpose eq21 eq733
    | exact resolve eq733 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq742 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq739 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq739
    | exact resolve eq739 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739
  have eq750 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq742 (M.op X0 X0)
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq742
    | exact resolve eq742 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq758 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq44 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq742 X0
       grind)
    | exact superpose eq742 eq44
    | exact resolve eq44 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq770 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq750 X0
       have i₂ := eq742 X0
       grind)
    | exact superpose eq742 eq750
    | exact resolve eq750 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq776 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq95 (M.op X0 X0) X1
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq95
    | exact resolve eq95 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq794 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq94 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq95 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq95 eq94
    | exact resolve eq94 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq806 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq794 X0
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq794
    | exact resolve eq794 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794
  have eq810 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq776 X0 X1
       have i₂ := eq742 X0
       grind)
    | exact superpose eq742 eq776
    | exact resolve eq776 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq839 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq69
    | exact resolve eq69 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq872 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq839 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq839
    | (have j0 := eq839 X0 X1
       grind)
    | exact resolve eq839 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839
  have eq885 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq806 X0
       grind)
    | exact superpose eq806 eq8
    | exact resolve eq8 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq895 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) X0)) := by
    intro X0
    first
    | (have i₁ := eq91 (M.op X0 (M.op X0 X0))
       have i₂ := eq806 X0
       grind)
    | exact superpose eq806 eq91
    | exact resolve eq91 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq924 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq895 X0
       have i₂ := eq770 X0
       grind)
    | exact superpose eq770 eq895
    | exact resolve eq895 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895
  have eq942 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq64 x y
       grind)
    | exact superpose eq64 eq14
    | (have j1 := eq64 x y
       grind)
    | exact resolve eq14 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq967 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq11
    | (have j0 := eq11 (σ X0) (σ X1)
       have j1 := eq64 X0 X1
       grind)
    | exact resolve eq11 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq977 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq967 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq967
    | (have j0 := eq967 X0 X1
       grind)
    | exact resolve eq967 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967
  have eq978 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq977 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq1030 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X1 X1)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq810 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq810 X0 X0
       grind)
    | exact superpose eq810 eq810
    | exact resolve eq810 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1073 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) = X0 ∨ (k (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))
       have i₂ := eq810 X0 X1
       grind)
    | exact superpose eq810 eq12
    | exact resolve eq12 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1081 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X1 (M.op X1 X1))) = X0 ∨ (k (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1073 X0 X1
       have i₂ := eq89 X1
       grind)
    | exact superpose eq89 eq1073
    | (have j0 := eq1073 X0 X1
       grind)
    | exact resolve eq1073 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073
  have eq1107 : ∀ X0 X1 : G, (k (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X0 X0))) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1081 X0 X1
       have i₂ := eq742 X1
       grind)
    | exact superpose eq742 eq1081
    | (have j0 := eq1081 X0 X1
       grind)
    | exact resolve eq1081 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081
  have eq1172 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X0) X1)) = (M.op X2 (M.op (M.op X2 X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq885 X1 X2
       have i₂ := eq885 X1 X0
       grind)
    | exact superpose eq885 eq885
    | exact resolve eq885 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1195 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op (M.op X0 X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq91 X1
       have i₂ := eq885 X1 X0
       grind)
    | exact superpose eq885 eq91
    | exact resolve eq91 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1196 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op (M.op X2 X2) (M.op X0 (M.op (M.op X0 X0) X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq94 X1 X2
       have i₂ := eq885 X1 X0
       grind)
    | exact superpose eq885 eq94
    | exact resolve eq94 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq1203 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) (M.op X1 (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq810 X1 X2
       have i₂ := eq885 X1 X0
       grind)
    | exact superpose eq885 eq810
    | exact resolve eq810 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1218 : ∀ X0 X1 : G, (k X1 (τ (M.op X0 (M.op (M.op X0 X0) (σ X1))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq142 X1
       have i₂ := eq885 (σ X1) X0
       grind)
    | exact superpose eq885 eq142
    | exact resolve eq142 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq1278 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq49
    | exact resolve eq49 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq1384 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1278 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1278
    | (have j0 := eq1278 X0 X1
       grind)
    | exact resolve eq1278 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1278
  have eq1398 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1195 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq810 X0 X0
       grind)
    | exact superpose eq810 eq1195
    | exact resolve eq1195 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1419 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1195 x (M.op X0 X0)
       have i₂ := eq8 X0 x
       grind)
    | exact superpose eq8 eq1195
    | exact resolve eq1195 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195
  have eq2708 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0))) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1398 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq1398 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq1398
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq1398 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1398
  have eq2806 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2708 X0 X1
       have i₂ := eq924 X0
       grind)
    | exact superpose eq924 eq2708
    | (have j0 := eq2708 X0 X1
       grind)
    | exact resolve eq2708 eq924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924 eq2708
  have eq3242 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (M.op (σ (τ X0)) (σ (τ X0))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq496 (τ X0) (τ X1)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq496
    | (have j0 := eq496 (τ X0) (τ X1)
       grind)
    | exact resolve eq496 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496
  have eq3268 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (τ (k X0 X1))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3242 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3242
    | (have j0 := eq3242 X0 X1
       grind)
    | exact resolve eq3242 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3242
  have eq3273 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3268 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq3268
    | (have j0 := eq3268 X0 X1
       grind)
    | exact resolve eq3268 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3268
  have eq3276 : ∀ X0 X1 : G, (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3273 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3273
    | (have j0 := eq3273 X0 X1
       grind)
    | exact resolve eq3273 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3273
  have eq3277 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3276 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3276
    | (have j0 := eq3276 X0 X1
       grind)
    | exact resolve eq3276 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3276
  have eq3544 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X0)) X1) ≠ X0 ∨ (M.op (M.op X0 (M.op X0 X0)) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3277 (M.op X1 (M.op X1 X1)) X1
       have i₂ := eq810 X1 X1
       grind)
    | exact superpose eq810 eq3277
    | exact resolve eq3277 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810 eq3277
  have eq4834 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0))) = (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1030 (M.op X1 X0) (M.op X1 (M.op X1 X1))
       have i₂ := eq1030 X0 X1
       grind)
    | exact superpose eq1030 eq1030
    | exact resolve eq1030 eq1030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5107 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0))) = (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op (M.op X1 X1) (M.op X1 (M.op X1 X1)))) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4834 X0 X1
       have i₂ := eq89 X1
       grind)
    | exact superpose eq89 eq4834
    | exact resolve eq4834 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq4834
  have eq5220 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0))) = (M.op (M.op (M.op X1 (M.op X1 X1)) X1) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5107 X0 X1
       have i₂ := eq742 X1
       grind)
    | exact superpose eq742 eq5107
    | exact resolve eq5107 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5107
  have eq5267 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5220 X0 X1
       have i₂ := eq770 X1
       grind)
    | exact superpose eq770 eq5220
    | exact resolve eq5220 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5220
  have eq12505 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq942
       have i₂ := eq872 y x
       grind)
    | exact superpose eq872 eq942
    | (have j1 := eq872 y x
       grind)
    | (have r₁ := eq942
       have r₂ := eq872 y x
       grind)
    | exact resolve eq942 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872 eq942
  have eq12506 : (σ (M.op x y)) = (σ x) ∨ x = (k x y) := by grind
  clear eq12505
  have eq12576 : (M.op x y) = (τ (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq12506
       grind)
    | exact superpose eq12506 eq9
    | exact resolve eq9 eq12506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12506
  have eq12631 : x = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq12576
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq12576
    | exact resolve eq12576 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12576
  have eq12632 : x = (k x y) := by
    first
    | (have j1 := eq70 x y
       grind)
    | (have r₁ := eq12631
       have r₂ := eq70 x y
       grind)
    | exact resolve eq12631 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq12631
  have eq18687 : ∀ X0 X1 : G, (k (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) (M.op (M.op X0 X0) (M.op X1 X1))) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1107 X1 (M.op X0 X0)
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq1107
    | (have j0 := eq1107 (k (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) (M.op (M.op X0 X0) (M.op X1 X1))) X1
       grind)
    | exact resolve eq1107 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107
  have eq18863 : ∀ X0 X1 : G, (k X0 (M.op (M.op X0 X0) (M.op X1 X1))) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18687 X0 X1
       have i₂ := eq742 X0
       grind)
    | exact superpose eq742 eq18687
    | (have j0 := eq18687 X0 X1
       grind)
    | exact resolve eq18687 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742 eq18687
  have eq27388 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 (M.op X1 X1)) (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1030 (M.op X1 (M.op X1 X1)) X0
       have i₂ := eq2806 X1 X0
       grind)
    | exact superpose eq2806 eq1030
    | (have j1 := eq2806 X1 X0
       grind)
    | exact resolve eq1030 eq2806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2806
  have eq27507 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 X1) (M.op (M.op X1 X1) (M.op (M.op X1 X1) (M.op X1 X1)))) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq27388 X0 X1
       have i₂ := eq5267 (M.op X1 X1) X1
       grind)
    | exact superpose eq5267 eq27388
    | (have j0 := eq27388 X0 X1
       grind)
    | exact resolve eq27388 eq5267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5267 eq27388
  have eq27666 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X0 X0)) X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq27507 X0 X1
       have i₂ := eq91 (M.op X1 X1)
       grind)
    | exact superpose eq91 eq27507
    | (have j0 := eq27507 X0 X1
       grind)
    | exact resolve eq27507 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27507
  have eq27714 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq27666 X0 X1
       have i₂ := eq770 X0
       grind)
    | exact superpose eq770 eq27666
    | (have j0 := eq27666 X0 X1
       grind)
    | exact resolve eq27666 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27666
  have eq28513 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X1 X1) X2)) (M.op X2 (M.op X0 X0))) = X3 ∨ (M.op X0 X3) = (k X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1203 X1 X2 X3
       have i₂ := eq27714 X3 X0
       grind)
    | (have i₁ := eq1203 X0 X1 X1
       have i₂ := eq27714 X0 X1
       grind)
    | exact superpose eq27714 eq1203
    | (have j1 := eq27714 X3 X0
       grind)
    | exact resolve eq1203 eq27714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27714
  have eq28864 : ∀ X0 X3 : G, (M.op X0 X3) = (k X0 X3) ∨ X0 = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq28513 X0 x x X3
       have i₂ := eq1203 x x X0
       grind)
    | exact superpose eq1203 eq28513
    | (have j0 := eq28513 X0 x x X3
       grind)
    | exact resolve eq28513 eq1203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203 eq28513
  have eq29351 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq28864 (σ X0) (σ X1)
       grind)
    | exact superpose eq28864 eq13
    | (have j1 := eq28864 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq13 eq28864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29374 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12632
       have i₂ := eq28864 x y
       grind)
    | exact superpose eq28864 eq12632
    | (have j1 := eq28864 x (M.op x y)
       grind)
    | exact resolve eq12632 eq28864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28864
  have eq30188 : (M.op y (M.op y y)) = (M.op (M.op x (M.op x x)) x) ∨ x = y := by
    first
    | (have i₁ := eq1030 y x
       have i₂ := eq29374
       grind)
    | exact superpose eq29374 eq1030
    | exact resolve eq1030 eq29374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030 eq29374
  have eq30203 : (M.op x x) = (M.op y (M.op y y)) ∨ x = y := by
    first
    | (have i₁ := eq30188
       have i₂ := eq770 x
       grind)
    | exact superpose eq770 eq30188
    | exact resolve eq30188 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770 eq30188
  have eq31434 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq978 (τ X1) (τ X0)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq978
    | exact resolve eq978 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978
  have eq31491 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq31434 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq31434
    | (have j0 := eq31434 X0 X1
       grind)
    | exact resolve eq31434 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31434
  have eq31495 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq31491 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq31491
    | (have j0 := eq31491 X0 X1
       grind)
    | exact resolve eq31491 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31491
  have eq31497 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31495 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq31495
    | (have j0 := eq31495 X0 X1
       grind)
    | exact resolve eq31495 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31495
  have eq31498 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31497 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq31497
    | (have j0 := eq31497 X0 X1
       grind)
    | exact resolve eq31497 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31497
  have eq36486 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31498 x (M.op (M.op x x) (M.op X0 (M.op X0 X0)))
       have i₂ := eq727 X0 x
       grind)
    | exact superpose eq727 eq31498
    | (have j1 := eq727 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq31498 x (M.op (M.op x x) (M.op x (M.op x x)))
       have r₂ := eq727 x x
       grind)
    | (have r₁ := eq31498 X0 X1
       have r₂ := eq727 (M.op X0 X0) (k X0 X1)
       grind)
    | (have r₁ := eq31498 X0 X1
       have r₂ := eq727 (k X0 X1) (M.op X0 X0)
       grind)
    | exact resolve eq31498 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq36493 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq31498 (M.op X0 X0) (M.op X0 (M.op X0 X0))
       have i₂ := eq758 X0
       grind)
    | exact superpose eq758 eq31498
    | (have j1 := eq758 X0
       grind)
    | exact resolve eq31498 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq36522 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) ≠ (τ (k X0 X1)) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31498 (τ X1) (τ X0)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq31498
    | exact resolve eq31498 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq31498
  have eq36530 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq36493 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36493
  have eq36548 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq36530 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq36530
    | (have j0 := eq36530 X0
       grind)
    | exact resolve eq36530 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq36530
  have eq37379 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X1)) ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq36548 X1
       have i₂ := eq885 X1 X0
       grind)
    | exact superpose eq885 eq36548
    | (have j0 := eq36548 X1
       grind)
    | exact resolve eq36548 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885 eq36548
  have eq39748 : y = (k y (M.op (M.op y y) (M.op x x))) ∨ x = y := by
    first
    | (have i₁ := eq104 y
       have i₂ := eq30203
       grind)
    | exact superpose eq30203 eq104
    | exact resolve eq104 eq30203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq30203
  have eq39861 : y = (k y (M.op (M.op y y) (M.op x x))) := by
    first
    | (have j1 := eq105 x y
       grind)
    | (have r₁ := eq39748
       have r₂ := eq105 y (k y (M.op (M.op y y) (M.op x x)))
       grind)
    | (have r₁ := eq39748
       have r₂ := eq105 (k y (M.op (M.op y y) (M.op x x))) y
       grind)
    | (have r₁ := eq39748
       have r₂ := eq105 x y
       grind)
    | exact resolve eq39748 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq39748
  have eq40235 : (σ y) = (σ (M.op y (M.op (M.op y y) (M.op x x)))) ∨ (M.op y y) = (M.op y (M.op (M.op y y) (M.op x x))) := by
    first
    | (have i₁ := eq1384 (M.op (M.op y y) (M.op x x)) y
       have i₂ := eq39861
       grind)
    | exact superpose eq39861 eq1384
    | (have j0 := eq1384 (M.op (M.op y y) (M.op x x)) y
       grind)
    | exact resolve eq1384 eq39861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1384 eq39861
  have eq40244 : (σ x) = (σ y) ∨ (M.op y y) = (M.op y (M.op (M.op y y) (M.op x x))) := by
    first
    | (have i₁ := eq40235
       have i₂ := eq8 x y
       grind)
    | exact superpose eq8 eq40235
    | exact resolve eq40235 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40235
  have eq40277 : x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq40244
       have i₂ := eq8 x y
       grind)
    | exact superpose eq8 eq40244
    | exact resolve eq40244 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40244
  have eq41585 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1419 y
       have i₂ := eq40277
       grind)
    | exact superpose eq40277 eq1419
    | exact resolve eq1419 eq40277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1419 eq40277
  have eq272295 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq29351 x y
       grind)
    | exact superpose eq29351 eq14
    | (have j1 := eq29351 x y
       grind)
    | exact resolve eq14 eq29351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29351
  have eq272304 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq272295
       have i₂ := eq12632
       grind)
    | exact superpose eq12632 eq272295
    | exact resolve eq272295 eq12632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12632 eq272295
  have eq272308 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq272304
       have i₂ := eq41585
       grind)
    | exact superpose eq41585 eq272304
    | exact resolve eq272304 eq41585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41585 eq272304
  have eq272320 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq272308
  have eq272321 : (σ x) = (σ y) := by grind
  clear eq272320
  have eq272325 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq272321
       grind)
    | exact superpose eq272321 eq9
    | exact resolve eq9 eq272321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272321
  have eq272399 : x = y := by
    first
    | (have i₁ := eq272325
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq272325
    | exact resolve eq272325 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272325
  have eq272403 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq272399
       grind)
    | exact superpose eq272399 eq14
    | exact resolve eq14 eq272399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272399
  have eq304788 : ∀ X0 X1 : G, (τ X0) ≠ (M.op (τ X1) (τ X1)) ∨ (τ X0) = (τ X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq36522 X0 (M.op (M.op X0 X0) (M.op X1 X1))
       have i₂ := eq18863 X0 X1
       grind)
    | exact superpose eq18863 eq36522
    | (have j1 := eq18863 X1 X0
       grind)
    | (have r₁ := eq36522 X0 X1
       have r₂ := eq18863 (τ X0) (τ (k X0 X1))
       grind)
    | exact resolve eq36522 eq18863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18863 eq36522
  have eq313420 : ∀ X0 X1 : G, (M.op (τ X1) (τ X1)) ≠ X0 ∨ (τ X1) = X0 ∨ (M.op X1 X1) = (σ X0) := by
    intro X0 X1
    first
    | (have i₁ := eq304788 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq304788
    | (have j0 := eq304788 (σ X0) X1
       grind)
    | (have r₁ := eq304788 (σ (M.op (τ X1) (τ X1))) X1
       have r₂ := eq9 (M.op (τ X1) (τ X1))
       grind)
    | exact resolve eq304788 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304788
  have eq313423 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ X0 = X1 ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq313420 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq313420
    | (have j0 := eq313420 X1 (σ X0)
       grind)
    | (have r₁ := eq313420 (τ (σ (M.op (τ X1) (τ X1)))) X1
       have r₂ := eq9 (M.op (τ X1) (τ X1))
       grind)
    | exact resolve eq313420 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313420
  have eq313430 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq313423 (M.op (σ X0) (σ X0)) (σ (M.op X0 X0))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313423
  have eq313443 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq272403
       have i₂ := eq313430 x
       grind)
    | exact superpose eq313430 eq272403
    | (have j1 := eq313430 x
       grind)
    | (have r₁ := eq272403
       have r₂ := eq313430 x
       grind)
    | exact resolve eq272403 eq313430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313430
  have eq313453 : x = (M.op x x) := by grind
  clear eq313443
  have eq313839 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X1)) = (M.op x (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1172 X0 X1 x
       have i₂ := eq313453
       grind)
    | exact superpose eq313453 eq1172
    | exact resolve eq1172 eq313453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172
  have eq313855 : ∀ X0 : G, (k X0 (τ (M.op x (M.op x (σ X0))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1218 x X0
       have i₂ := eq313453
       grind)
    | exact superpose eq313453 eq1218
    | exact resolve eq1218 eq313453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218
  have eq313907 : ∀ X0 : G, x ≠ (k (M.op x x) X0) ∨ x = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq3544 x x
       have i₂ := eq313453
       grind)
    | exact superpose eq313453 eq3544
    | exact resolve eq3544 eq313453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3544
  have eq314012 : ∀ X0 : G, (M.op X0 X0) ≠ x ∨ x = X0 ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq36486 x x
       have i₂ := eq313453
       grind)
    | exact superpose eq313453 eq36486
    | (have j0 := eq36486 x X0
       grind)
    | exact resolve eq36486 eq313453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36486
  have eq314017 : ∀ X0 : G, (M.op x (M.op x X0)) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq37379 x X0
       have i₂ := eq313453
       grind)
    | exact superpose eq313453 eq37379
    | (have j0 := eq37379 X0 X0
       grind)
    | exact resolve eq37379 eq313453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37379
  have eq314204 : ∀ X0 : G, (M.op X0 X0) ≠ x ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq314012 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314012
  have eq314287 : ∀ X0 : G, x ≠ (k x X0) ∨ x = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq313907 X0
       have i₂ := eq313453
       grind)
    | exact superpose eq313453 eq313907
    | (have j0 := eq313907 X0
       grind)
    | exact resolve eq313907 eq313453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313907
  have eq314392 : ∀ X0 : G, x ≠ (k x X0) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq314287 X0
       have i₂ := eq313453
       grind)
    | exact superpose eq313453 eq314287
    | (have j0 := eq314287 X0
       grind)
    | exact resolve eq314287 eq313453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314287
  have eq314443 : ∀ X0 X1 X2 : G, x ≠ (M.op X0 (M.op (M.op X0 X0) (M.op X1 (M.op (M.op X1 X1) X2)))) ∨ x = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq314204 X2
       have i₂ := eq1196 X1 X2 X0
       grind)
    | exact superpose eq1196 eq314204
    | (have j0 := eq314204 X2
       grind)
    | exact resolve eq314204 eq1196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196 eq314204
  have eq314526 : ∀ X1 X2 : G, x ≠ (M.op x (M.op x (M.op X1 (M.op (M.op X1 X1) X2)))) ∨ x = X2 := by
    intro X1 X2
    first
    | (have i₁ := eq314443 x X1 X2
       have i₂ := eq313839 x (M.op X1 (M.op (M.op X1 X1) X2))
       grind)
    | exact superpose eq313839 eq314443
    | (have j0 := eq314443 x X1 X2
       grind)
    | exact resolve eq314443 eq313839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314443
  have eq314529 : ∀ X2 : G, x ≠ (M.op x (M.op x (M.op x (M.op x X2)))) ∨ x = X2 := by
    intro X2
    first
    | (have i₁ := eq314526 x X2
       have i₂ := eq313839 x X2
       grind)
    | exact superpose eq313839 eq314526
    | (have j0 := eq314526 x X2
       grind)
    | exact resolve eq314526 eq313839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313839 eq314526
  have eq315721 : x ≠ x ∨ x = (M.op x (τ (M.op x (M.op x (σ x))))) := by
    first
    | (have i₁ := eq314392 (τ (M.op x (M.op x (σ x))))
       have i₂ := eq313855 x
       grind)
    | exact superpose eq313855 eq314392
    | (have j0 := eq314392 (τ (M.op x (M.op x (σ x))))
       grind)
    | (have r₁ := eq314392 (τ (M.op x (M.op x (σ x))))
       have r₂ := eq313855 x
       grind)
    | exact resolve eq314392 eq313855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313855 eq314392
  have eq315727 : x = (M.op x (τ (M.op x (M.op x (σ x))))) := by grind
  clear eq315721
  have eq321271 : x ≠ (M.op x (M.op x (M.op x x))) ∨ x = (τ (M.op x (M.op x (σ x)))) := by
    first
    | (have i₁ := eq314529 (τ (M.op x (M.op x (σ x))))
       have i₂ := eq315727
       grind)
    | exact superpose eq315727 eq314529
    | (have j0 := eq314529 (τ (M.op x (M.op x (σ x))))
       grind)
    | exact resolve eq314529 eq315727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314529 eq315727
  have eq321319 : x = (τ (M.op x (M.op x (σ x)))) := by
    first
    | (have r₁ := eq321271
       have r₂ := eq91 x
       grind)
    | exact resolve eq321271 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq321271
  have eq321333 : (σ x) = (M.op x (M.op x (σ x))) := by
    first
    | (have i₁ := eq10 (M.op x (M.op x (σ x)))
       have i₂ := eq321319
       grind)
    | exact superpose eq321319 eq10
    | exact resolve eq10 eq321319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321319
  have eq321487 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq314017 (σ x)
       have i₂ := eq321333
       grind)
    | exact superpose eq321333 eq314017
    | (have j0 := eq314017 (σ x)
       grind)
    | (have r₁ := eq314017 (σ x)
       have r₂ := eq321333
       grind)
    | exact resolve eq314017 eq321333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314017 eq321333
  have eq321534 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq321487
  have eq321597 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq272403
       have i₂ := eq321534
       grind)
    | exact superpose eq321534 eq272403
    | exact resolve eq272403 eq321534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272403 eq321534
  have eq322149 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq321597
       have i₂ := eq313453
       grind)
    | exact superpose eq313453 eq321597
    | exact resolve eq321597 eq313453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313453 eq321597
  have eq322150 : False := by grind
  exact eq322150

/-- `Equation947`: `x = y ◇ ((z ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyx_y_x_pxy_Equation947 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law947 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law947.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X0)) = (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X3 X0) (M.op X2 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op (M.op X3 X0) (M.op X2 X0)) X1 X2
       have i₂ := eq8 X0 X2 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 (M.op (M.op X3 X0) (M.op X1 X0))) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op (M.op X3 X0) (M.op X1 X0)) X1 X2
       have i₂ := eq8 X0 X1 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op (M.op X2 X0) (M.op X1 X0)) = (k (M.op (M.op X2 X0) (M.op X1 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (M.op (M.op X2 X0) (M.op X1 X0)) X1
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq11
    | (have j0 := eq11 (M.op (M.op X2 X0) (M.op X1 X0)) X1
       grind)
    | (have r₁ := eq11 (M.op (M.op X2 X0) (M.op X0 X0)) X0
       have r₂ := eq8 X0 X0 X2
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9
    | exact resolve eq9 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 (τ X0) X1
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (σ X0) (M.op (M.op X1 (σ X2)) (σ X0))) ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (σ X2) (σ X0) X1
       have i₂ := eq25 X2 X0
       grind)
    | exact superpose eq25 eq8
    | (have j1 := eq25 X2 X0
       grind)
    | exact resolve eq8 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (σ X2) = (M.op X1 (M.op (σ X0) (M.op X1 (σ X2)))) ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (σ X2) X1 (σ X0)
       have i₂ := eq25 X2 X0
       grind)
    | exact superpose eq25 eq8
    | (have j1 := eq25 X2 X0
       grind)
    | exact resolve eq8 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       have j1 := eq25 X1 X0
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq25 X0 X1
       grind)
    | exact resolve eq11 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq25 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq58 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq57
    | (have j0 := eq57 X0 X1
       grind)
    | exact resolve eq57 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq64 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23
    | exact resolve eq23 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = (k (M.op (M.op X0 X1) (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq19 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq95 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X2 X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 X2 X2 X1
       have i₂ := eq8 X0 X2 X1
       grind)
    | exact superpose eq8 eq17
    | exact resolve eq17 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X0 X1) (M.op (M.op X2 X1) X1))) (M.op (M.op X0 X1) (M.op (M.op X2 X1) X1))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 (M.op X3 (M.op (M.op X0 X1) (M.op (M.op X2 X1) X1))) X2
       have i₂ := eq18 X1 (M.op X2 X1) X3 X0
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq134 : ∀ X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X2 X1) (M.op X1 X1))) (M.op (M.op X2 X1) (M.op X1 X1))) = X1 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq133 X1 x X2 X3
       have i₂ := eq95 x X1 (M.op X2 x)
       grind)
    | exact superpose eq95 eq133
    | exact resolve eq133 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq147 : ∀ X1 X3 : G, (M.op (M.op X3 (M.op X1 (M.op X1 X1))) (M.op X1 (M.op X1 X1))) = X1 := by
    intro X1 X3
    first
    | (have i₁ := eq134 x X1 X3
       have i₂ := eq95 x X1 x
       grind)
    | exact superpose eq95 eq134
    | exact resolve eq134 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq168 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 x
       have i₂ := eq95 X1 x X0
       grind)
    | exact superpose eq95 eq8
    | exact resolve eq8 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq168 X2 (M.op X0 X1)
       have i₂ := eq95 X1 X0 X0
       grind)
    | exact superpose eq95 eq168
    | exact resolve eq168 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq168 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq168 (M.op X0 X0) X0
       grind)
    | exact superpose eq168 eq168
    | exact resolve eq168 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq168 (M.op X1 X0) X0
       have i₂ := eq95 X0 X1 X0
       grind)
    | exact superpose eq95 eq168
    | exact resolve eq168 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X1 X0 X0
       have i₂ := eq168 X1 (M.op X0 X1)
       grind)
    | exact superpose eq168 eq17
    | exact resolve eq17 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq240 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X0))) X0) = (M.op X2 (M.op (M.op X2 (M.op X0 X0)) (M.op X2 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq95 (M.op X2 (M.op X0 X0)) X1 X2
       have i₂ := eq168 X2 X0
       grind)
    | exact superpose eq168 eq95
    | exact resolve eq95 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X0 X0) (M.op X1 (M.op X0 X0)) X1
       have i₂ := eq168 (M.op X1 (M.op X0 X0)) X0
       grind)
    | exact superpose eq168 eq8
    | exact resolve eq8 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq240 X0 X1 X2
       have i₂ := eq8 (M.op X0 X0) X2 X2
       grind)
    | exact superpose eq8 eq240
    | exact resolve eq240 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq251 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq232 X0 X1
       have i₂ := eq95 X1 X0 X0
       grind)
    | exact superpose eq95 eq232
    | exact resolve eq232 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq283 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X1 X0) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X1 (M.op X0 X0)
       have i₂ := eq228 X0
       grind)
    | exact superpose eq228 eq95
    | exact resolve eq95 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq291 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X0 (M.op (M.op X1 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq283 X0 X1
       have i₂ := eq251 (M.op X1 X0) X0
       grind)
    | exact superpose eq251 eq283
    | exact resolve eq283 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq296 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq291 X0 X1
       have i₂ := eq251 (M.op X0 X0) X0
       grind)
    | exact superpose eq251 eq291
    | exact resolve eq291 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq300 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X0 (M.op (M.op X1 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq296 X0 X1
       have i₂ := eq228 X0
       grind)
    | exact superpose eq228 eq296
    | exact resolve eq296 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq437 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq147 (M.op X1 X1) x
       have i₂ := eq168 (M.op X1 X1) X1
       grind)
    | exact superpose eq168 eq147
    | exact resolve eq147 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq448 : ∀ X0 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X0 X0)))) = (M.op X2 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X2
    first
    | (have i₁ := eq95 (M.op X0 (M.op X0 X0)) (M.op x (M.op X0 (M.op X0 X0))) X2
       have i₂ := eq147 X0 x
       grind)
    | exact superpose eq147 eq95
    | exact resolve eq95 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq449 : ∀ X0 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X0 X0)))) = (M.op X2 (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X2
    first
    | (have i₁ := eq448 X0 X2
       have i₂ := eq95 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq95 eq448
    | exact resolve eq448 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq458 : ∀ X0 X2 : G, (M.op X2 X0) = (M.op X0 (M.op X2 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X2
    first
    | (have i₁ := eq449 X0 X2
       have i₂ := eq8 X0 X0 X0
       grind)
    | exact superpose eq8 eq449
    | exact resolve eq449 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449
  have eq471 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0))) = (M.op X0 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq437 (M.op X1 (M.op X0 X0)) X1
       have i₂ := eq168 X1 X0
       grind)
    | exact superpose eq168 eq437
    | exact resolve eq437 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq503 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op X0 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq471 X0 X1
       have i₂ := eq95 (M.op X0 X0) X1 X1
       grind)
    | exact superpose eq95 eq471
    | exact resolve eq471 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471
  have eq512 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X0))) = (M.op X1 (M.op X0 (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq503 X0 X1
       have i₂ := eq251 (M.op X0 X0) X0
       grind)
    | exact superpose eq251 eq503
    | exact resolve eq503 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq516 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq512 X0 X1
       have i₂ := eq300 X0 X0
       grind)
    | exact superpose eq300 eq512
    | exact resolve eq512 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300 eq512
  have eq525 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq26
    | exact resolve eq26 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq561 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq525 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq525
    | (have j0 := eq525 X0 X1
       grind)
    | exact resolve eq525 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525
  have eq695 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq58
    | exact resolve eq58 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq706 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq58 y x
       grind)
    | exact superpose eq58 eq14
    | (have j1 := eq58 y x
       grind)
    | exact resolve eq14 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq707 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 X0
       have i₂ := eq58 X1 X0
       grind)
    | exact superpose eq58 eq25
    | (have j0 := eq25 X1 X0
       have j1 := eq58 X0 X1
       grind)
    | exact resolve eq25 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq725 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq707 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq732 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq695 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq695
    | (have j0 := eq695 X0 X1
       grind)
    | exact resolve eq695 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq735 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq732 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq732
    | (have j0 := eq732 X0 X1
       grind)
    | exact resolve eq732 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq858 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq168 X1 X0
       have i₂ := eq251 X1 X0
       grind)
    | (have i₁ := eq168 X1 X1
       have i₂ := eq251 X1 X1
       grind)
    | exact superpose eq251 eq168
    | exact resolve eq168 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1102 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0)))) = (k (M.op X0 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0)))) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X1 (M.op X0 (M.op X1 X0))
       have i₂ := eq858 X0 X1
       grind)
    | exact superpose eq858 eq73
    | exact resolve eq73 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq1107 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq437 (M.op X0 (M.op X1 X0)) X1
       have i₂ := eq858 X0 X1
       grind)
    | exact superpose eq858 eq437
    | exact resolve eq437 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1109 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X0))) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1107 X0 X1
       have i₂ := eq95 (M.op X1 X0) X0 X0
       grind)
    | exact superpose eq95 eq1107
    | exact resolve eq1107 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107
  have eq1114 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1102 x X1
       have i₂ := eq8 (M.op X1 x) x x
       grind)
    | exact superpose eq8 eq1102
    | exact resolve eq1102 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102
  have eq1126 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1109 X0 X1
       have i₂ := eq95 X0 X1 X1
       grind)
    | exact superpose eq95 eq1109
    | exact resolve eq1109 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109
  have eq1152 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X0) (M.op (σ X2) (σ X0))) ∨ (σ (k X1 X2)) = (M.op (σ X1) (σ X2)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X2 (σ X0) X1
       have i₂ := eq25 X1 X0
       grind)
    | exact superpose eq25 eq54
    | (have j0 := eq54 X2 X1 X1
       have j1 := eq25 X1 X2
       grind)
    | exact resolve eq54 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq54
  have eq1534 : ∀ X0 X1 X2 : G, (M.op (σ X1) (M.op (M.op X2 X0) (σ X1))) = X0 ∨ (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq53
    | exact resolve eq53 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1583 : ∀ X0 X1 X2 : G, (M.op (σ X1) (M.op (M.op X2 X0) (σ X1))) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1534 X0 X1 X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1534
    | (have j0 := eq1534 X0 X1 X2
       grind)
    | exact resolve eq1534 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1534
  have eq1590 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq227 X1 (M.op X1 X0) X2
       have i₂ := eq8 X0 X1 X1
       grind)
    | exact superpose eq8 eq227
    | exact resolve eq227 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2020 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq227 X1 X1 X2
       have i₂ := eq1590 X1 X1 X0
       grind)
    | (have i₁ := eq227 X1 X1 X2
       have i₂ := eq1590 X1 X0 X1
       grind)
    | exact superpose eq1590 eq227
    | exact resolve eq227 eq1590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq2022 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq168 X1 X1
       have i₂ := eq1590 X1 X1 X0
       grind)
    | (have i₁ := eq168 X1 X1
       have i₂ := eq1590 X1 X0 X1
       grind)
    | exact superpose eq1590 eq168
    | exact resolve eq168 eq1590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2057 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 (M.op X2 X1) X2
       have i₂ := eq1590 X1 (M.op X2 X1) X0
       grind)
    | (have i₁ := eq8 X1 (M.op X2 X1) X2
       have i₂ := eq1590 X1 X0 (M.op X2 X1)
       grind)
    | exact superpose eq1590 eq8
    | exact resolve eq8 eq1590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3038 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X2 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq458 X0 (M.op X1 (M.op X2 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))))
       have i₂ := eq249 (M.op X0 (M.op X0 X0)) X1 X2
       grind)
    | exact superpose eq249 eq458
    | exact resolve eq458 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249 eq458
  have eq3051 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)))) = (M.op (M.op X1 (M.op X2 (M.op X0 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0))))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3038 X0 X1 X2
       have i₂ := eq516 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq516 eq3038
    | exact resolve eq3038 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516 eq3038
  have eq3072 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X0 (M.op (M.op X0 (M.op X0 X0)) X0)))) = (M.op (M.op X1 (M.op X2 (M.op X0 (M.op X0 (M.op (M.op X0 (M.op X0 X0)) X0))))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3051 X0 X1 X2
       have i₂ := eq1126 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq1126 eq3051
    | exact resolve eq3051 eq1126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126 eq3051
  have eq3092 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X2 (M.op X0 (M.op X0 (M.op X0 X0))))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3072 X0 X1 X2
       have i₂ := eq245 X0 X0
       grind)
    | exact superpose eq245 eq3072
    | exact resolve eq3072 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245 eq3072
  have eq3102 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3092 X0 X1 X2
       have i₂ := eq858 X0 X0
       grind)
    | exact superpose eq858 eq3092
    | exact resolve eq3092 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3092
  have eq9090 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2020 X1 X2 X1
       have i₂ := eq1590 (M.op X1 X2) X1 X0
       grind)
    | (have i₁ := eq2020 X1 X2 X1
       have i₂ := eq1590 (M.op X1 X2) X0 X1
       grind)
    | exact superpose eq1590 eq2020
    | exact resolve eq2020 eq1590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20269 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op X3 (M.op X0 (M.op X1 (M.op X1 (M.op X0 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq251 X3 X2
       have i₂ := eq9090 X1 X0 X2
       grind)
    | exact superpose eq9090 eq251
    | exact resolve eq251 eq9090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20402 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X1 (M.op X1 (M.op X0 (M.op X2 X3)))))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 X2 X2
       have i₂ := eq9090 X1 X0 (M.op X2 X3)
       grind)
    | exact superpose eq9090 eq8
    | exact resolve eq8 eq9090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28465 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq735 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq735
    | exact resolve eq735 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq28976 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq706
       have i₂ := eq561 x y
       grind)
    | exact superpose eq561 eq706
    | (have j1 := eq561 x y
       grind)
    | (have r₁ := eq706
       have r₂ := eq561 x y
       grind)
    | exact resolve eq706 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561 eq706
  have eq28977 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by grind
  clear eq28976
  have eq32104 : (M.op x y) = (τ (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq28977
       grind)
    | exact superpose eq28977 eq9
    | exact resolve eq9 eq28977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28977
  have eq32173 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq32104
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq32104
    | exact resolve eq32104 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32104
  have eq32518 : ∀ X0 : G, (M.op x x) = (M.op y (M.op X0 (M.op X0 y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9090 X0 y x
       have i₂ := eq32173
       grind)
    | exact superpose eq32173 eq9090
    | exact resolve eq9090 eq32173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9090 eq32173
  have eq32530 : x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq32518 x
       have i₂ := eq2022 x y
       grind)
    | exact superpose eq2022 eq32518
    | exact resolve eq32518 eq2022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32518
  have eq32561 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq725 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq725
    | exact resolve eq725 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32634 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq725 X1 X0
       grind)
    | exact superpose eq725 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       have j1 := eq725 X1 X0
       grind)
    | exact resolve eq11 eq725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725
  have eq32694 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32634 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq32634
    | (have j0 := eq32634 X0 X1
       grind)
    | exact resolve eq32634 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32634
  have eq32695 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq32694 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32694
  have eq32707 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq32561 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq32561
    | (have j0 := eq32561 X0 X1
       grind)
    | exact resolve eq32561 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32561
  have eq32713 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq32707 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq32707
    | (have j0 := eq32707 X0 X1
       grind)
    | exact resolve eq32707 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq32707
  have eq35665 : x ≠ x ∨ y = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq32530
       grind)
    | exact superpose eq32530 eq11
    | (have j0 := eq11 y x
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq32530
       grind)
    | exact resolve eq11 eq32530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35690 : y = (M.op x (M.op y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq858 y x
       have i₂ := eq32530
       grind)
    | exact superpose eq32530 eq858
    | exact resolve eq858 eq32530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32530
  have eq35723 : y = (k y x) ∨ y = (M.op x x) := by grind
  clear eq35665
  have eq46908 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (M.op X1 X0) X0) ∨ (M.op X0 (σ X2)) = (k X0 (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq858 (σ X2) (M.op X1 X0)
       have i₂ := eq1583 X0 X2 X1
       grind)
    | exact superpose eq1583 eq858
    | (have j1 := eq1583 X0 X2 X2
       grind)
    | exact resolve eq858 eq1583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1583
  have eq47029 : ∀ X0 X2 : G, (σ X2) = (M.op X0 X0) ∨ (M.op X0 (σ X2)) = (k X0 (σ X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq46908 X0 x X2
       have i₂ := eq437 X0 x
       grind)
    | exact superpose eq437 eq46908
    | (have j0 := eq46908 X0 x X2
       grind)
    | exact resolve eq46908 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46908
  have eq60923 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq32695 (τ X0) (τ X1)
       have i₂ := eq64 X1 X0
       grind)
    | exact superpose eq64 eq32695
    | (have j0 := eq32695 (τ X0) (τ X1)
       grind)
    | exact resolve eq32695 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60934 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq32695 y x
       have i₂ := eq35723
       grind)
    | exact superpose eq35723 eq32695
    | (have j0 := eq32695 y x
       grind)
    | exact resolve eq32695 eq35723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32695 eq35723
  have eq60966 : (σ x) = (σ (k x y)) ∨ y = (M.op x x) := by grind
  clear eq60934
  have eq61019 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq60923 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq60923
    | (have j0 := eq60923 X0 X1
       grind)
    | exact resolve eq60923 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60923
  have eq61044 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq61019 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq61019
    | (have j0 := eq61019 X0 X1
       grind)
    | exact resolve eq61019 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61019
  have eq61064 : ∀ X0 X1 : G, (σ (τ X1)) = (k (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq61044 X0 X1
       have i₂ := eq16 X0 (τ X1)
       grind)
    | exact superpose eq16 eq61044
    | (have j0 := eq61044 X0 X1
       grind)
    | exact resolve eq61044 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61044
  have eq61067 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61064 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq61064
    | (have j0 := eq61064 X0 X1
       grind)
    | exact resolve eq61064 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61064
  have eq164954 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 (σ X1)
       have i₂ := eq32713 (σ X0) X1
       grind)
    | exact superpose eq32713 eq33
    | (have j1 := eq32713 (σ X0) X1
       grind)
    | exact resolve eq33 eq32713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32713
  have eq165238 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq164954 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq164954
    | (have j0 := eq164954 X0 X1
       grind)
    | exact resolve eq164954 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164954
  have eq165294 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq165238 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq165238
    | (have j0 := eq165238 X0 X1
       grind)
    | exact resolve eq165238 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165238
  have eq165302 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq165294 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq165294
    | (have j0 := eq165294 X0 X1
       grind)
    | exact resolve eq165294 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165294
  have eq207624 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq165302 y x
       grind)
    | exact superpose eq165302 eq14
    | (have j1 := eq165302 y x
       grind)
    | exact resolve eq14 eq165302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207692 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (k X0 X0)))) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq168 X1 (σ X0)
       have i₂ := eq165302 X0 X0
       grind)
    | exact superpose eq165302 eq168
    | (have j1 := eq165302 X0 X0
       grind)
    | exact resolve eq168 eq165302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207710 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq228 (σ X0)
       have i₂ := eq165302 X0 X0
       grind)
    | exact superpose eq165302 eq228
    | (have j1 := eq165302 X0 X0
       grind)
    | exact resolve eq228 eq165302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228 eq165302
  have eq208259 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq207624
       have i₂ := eq28465 y x
       grind)
    | exact superpose eq28465 eq207624
    | (have j1 := eq28465 x y
       grind)
    | exact resolve eq207624 eq28465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28465 eq207624
  have eq208268 : y = (k y x) ∨ x = (k x y) := by grind
  clear eq208259
  have eq210293 : y ≠ y ∨ x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq61067 y x
       have i₂ := eq208268
       grind)
    | exact superpose eq208268 eq61067
    | (have j0 := eq61067 y x
       grind)
    | (have r₁ := eq61067 y x
       have r₂ := eq208268
       grind)
    | (have r₁ := eq61067 x y
       have r₂ := eq208268
       grind)
    | exact resolve eq61067 eq208268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208268
  have eq210298 : y ≠ y ∨ x = (k x y) := by grind
  clear eq210293
  have eq210299 : x = (k x y) := by grind
  clear eq210298
  have eq211089 : x ≠ x ∨ y = (k y x) := by
    first
    | (have i₁ := eq61067 x y
       have i₂ := eq210299
       grind)
    | exact superpose eq210299 eq61067
    | (have j0 := eq61067 x y
       grind)
    | (have r₁ := eq61067 x y
       have r₂ := eq210299
       grind)
    | exact resolve eq61067 eq210299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61067 eq210299
  have eq211092 : y = (k y x) := by grind
  clear eq211089
  have eq213306 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (M.op (σ X1) (σ X1))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1152 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1152
  have eq213307 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (M.op (σ X1) (σ X1))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq213306 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213306
  have eq258362 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq47029 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq47029
    | exact resolve eq47029 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258602 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq47029 X0 X1
       grind)
    | exact superpose eq47029 eq23
    | (have j1 := eq47029 X0 X1
       grind)
    | exact resolve eq23 eq47029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq47029
  have eq259066 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq258362 (τ X1) X0
       grind)
    | exact superpose eq258362 eq16
    | (have j1 := eq258362 (τ X1) X0
       grind)
    | exact resolve eq16 eq258362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq259109 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq60966
       have i₂ := eq258362 y x
       grind)
    | exact superpose eq258362 eq60966
    | (have j1 := eq258362 y x
       grind)
    | exact resolve eq60966 eq258362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60966
  have eq259244 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq229 X1 X1
       have i₂ := eq258362 X0 X1
       grind)
    | (have i₁ := eq229 X0 X1
       have i₂ := eq258362 (M.op X1 X0) X1
       grind)
    | exact superpose eq258362 eq229
    | (have j1 := eq258362 X0 X1
       grind)
    | exact resolve eq229 eq258362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259270 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2022 X1 X1
       have i₂ := eq258362 X0 X1
       grind)
    | (have i₁ := eq2022 X0 X1
       have i₂ := eq258362 (M.op X0 X1) X1
       grind)
    | exact superpose eq258362 eq2022
    | (have j1 := eq258362 X0 X1
       grind)
    | exact resolve eq2022 eq258362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2022
  have eq259413 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq259109
  have eq267582 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 (M.op X0 X1))) = X2 ∨ (M.op X0 (M.op X0 X1)) = (k X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq259244 (M.op X1 X0) X1
       have i₂ := eq1590 X0 X1 X2
       grind)
    | (have i₁ := eq259244 (M.op X2 X0) X2
       have i₂ := eq1590 X0 X1 X2
       grind)
    | exact superpose eq1590 eq259244
    | exact resolve eq259244 eq1590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1590
  have eq267583 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = X1 ∨ (k X1 (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq259244 (M.op X0 (M.op X1 X0)) X1
       have i₂ := eq858 X0 X1
       grind)
    | exact superpose eq858 eq259244
    | exact resolve eq259244 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259244
  have eq267985 : ∀ X0 X1 : G, (k X1 (M.op X0 (M.op X1 X0))) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq267583 X0 X1
       have i₂ := eq3102 X0 X0 X1
       grind)
    | exact superpose eq3102 eq267583
    | (have j0 := eq267583 X0 X1
       grind)
    | exact resolve eq267583 eq3102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267583
  have eq267986 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (k X2 (M.op X2 X1)) ∨ X1 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq267582 X0 X1 X2
       have i₂ := eq2057 X0 X1 X2
       grind)
    | exact superpose eq2057 eq267582
    | (have j0 := eq267582 X0 X1 X2
       grind)
    | exact resolve eq267582 eq2057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267582
  have eq269508 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = X1 ∨ (M.op X0 (M.op X1 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq259270 (M.op X1 X1) X0
       have i₂ := eq251 X0 X1
       grind)
    | (have i₁ := eq259270 (M.op X0 X1) X1
       have i₂ := eq251 X0 X1
       grind)
    | exact superpose eq251 eq259270
    | exact resolve eq259270 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251 eq259270
  have eq269935 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k X1 (M.op X0 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq269508 X0 X1
       have i₂ := eq858 X0 X1
       grind)
    | exact superpose eq858 eq269508
    | (have j0 := eq269508 X0 X1
       grind)
    | exact resolve eq269508 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269508
  have eq275904 : x = (k y y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq267985 x y
       have i₂ := eq35690
       grind)
    | exact superpose eq35690 eq267985
    | (have j0 := eq267985 x y
       grind)
    | exact resolve eq267985 eq35690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35690 eq267985
  have eq275929 : x = (k y y) ∨ y = (M.op x x) := by grind
  clear eq275904
  have eq277206 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (k X0 (M.op X0 X1))) = X1 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 (M.op X2 X1) X2
       have i₂ := eq267986 (M.op X2 X1) X1 X0
       grind)
    | exact superpose eq267986 eq8
    | (have j1 := eq267986 X0 (M.op (M.op X2 X1) (k X0 (M.op X0 X1))) X1
       grind)
    | exact resolve eq8 eq267986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq442102 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq207692 X0 X1
       have i₂ := eq258362 X0 X0
       grind)
    | exact superpose eq258362 eq207692
    | (have j1 := eq258362 X0 X0
       grind)
    | exact resolve eq207692 eq258362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207692 eq258362
  have eq442170 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq442102 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442102
  have eq461013 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq258602 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq258602
    | exact resolve eq258602 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258602
  have eq461076 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq461013 X0 X1
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq461013
    | (have j0 := eq461013 X0 X1
       grind)
    | exact resolve eq461013 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq461013
  have eq461807 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 ∨ (τ (k X1 X0)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq229 X1 X1
       have i₂ := eq461076 X0 X1
       grind)
    | (have i₁ := eq229 X0 X1
       have i₂ := eq461076 (M.op X1 X0) X1
       grind)
    | exact superpose eq461076 eq229
    | (have j1 := eq461076 X0 X1
       grind)
    | exact resolve eq229 eq461076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229 eq461076
  have eq506765 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq259066 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq259066
    | exact resolve eq259066 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq506776 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq259066 X0 X1
       grind)
    | exact superpose eq259066 eq10
    | (have j1 := eq259066 X0 X1
       grind)
    | exact resolve eq10 eq259066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259066
  have eq506831 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq506765 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq506765
    | (have j0 := eq506765 X0 X1
       grind)
    | exact resolve eq506765 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506765
  have eq507494 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X0)) = X2 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq168 X1 X2
       have i₂ := eq506831 X0 X2
       grind)
    | (have i₁ := eq168 X0 X1
       have i₂ := eq506831 (M.op X1 X1) X1
       grind)
    | exact superpose eq506831 eq168
    | (have j1 := eq506831 X0 X2
       grind)
    | exact resolve eq168 eq506831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506831
  have eq651175 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X0 X1))) = (τ (k X0 (M.op X0 X1))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2057 X0 X1 X0
       have i₂ := eq461807 (M.op X0 X1) X0
       grind)
    | exact superpose eq461807 eq2057
    | (have j1 := eq461807 (M.op X0 X1) X0
       grind)
    | exact resolve eq2057 eq461807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2057 eq461807
  have eq663728 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq506776 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq506776
    | (have j0 := eq506776 X1 (σ X0)
       grind)
    | exact resolve eq506776 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506776
  have eq663745 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq663728 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq663728
    | (have j0 := eq663728 X0 X1
       grind)
    | exact resolve eq663728 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663728
  have eq724590 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 X1))) = (σ (k X0 (M.op X1 X1))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq858 X1 X1
       have i₂ := eq507494 (M.op X1 X1) X1 X0
       grind)
    | (have i₁ := eq858 X0 X1
       have i₂ := eq507494 X0 X1 (M.op X1 (M.op X0 (M.op X1 X0)))
       grind)
    | exact superpose eq507494 eq858
    | (have j1 := eq507494 (M.op X1 X1) X1 X0
       grind)
    | exact resolve eq858 eq507494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858 eq507494
  have eq726987 : ∀ X0 X1 X2 : G, (τ (M.op X0 (M.op X0 X1))) = (τ (M.op X2 (M.op X2 X1))) ∨ X1 = X2 ∨ X1 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq651175 X2 X1
       have i₂ := eq267986 X0 X1 X2
       grind)
    | exact superpose eq267986 eq651175
    | (have j0 := eq651175 (τ (M.op X0 (M.op X0 X1))) (τ (M.op X2 (M.op X2 X1)))
       have j1 := eq267986 X0 (τ (M.op X0 (M.op X0 X1))) (τ (M.op X2 (M.op X2 X1)))
       grind)
    | exact resolve eq651175 eq267986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267986 eq651175
  have eq727008 : ∀ X0 X1 X2 : G, (τ (M.op X0 (M.op X0 X1))) = (τ (M.op X2 (M.op X2 X1))) ∨ X1 = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq726987 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726987
  have eq727422 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq663745 x y
       have i₂ := eq211092
       grind)
    | exact superpose eq211092 eq663745
    | (have j0 := eq663745 x y
       grind)
    | exact resolve eq663745 eq211092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663745
  have eq745491 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 X0))) = (σ (M.op X1 (M.op X0 X0))) ∨ X0 = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq724590 X1 X0
       have i₂ := eq269935 X0 X1
       grind)
    | exact superpose eq269935 eq724590
    | (have j0 := eq724590 (σ (M.op X0 (M.op X1 X0))) (σ (M.op X1 (M.op X0 X0)))
       have j1 := eq269935 (σ (M.op X0 (M.op X1 X0))) (σ (M.op X1 (M.op X0 X0)))
       grind)
    | exact resolve eq724590 eq269935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269935 eq724590
  have eq745508 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 X0))) = (σ (M.op X1 (M.op X0 X0))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq745491 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745491
  have eq746277 : ∀ X0 X1 X2 X3 : G, (τ (M.op X0 (M.op X0 X1))) = (τ (M.op X2 (M.op X2 X1))) ∨ X1 = X3 ∨ X1 = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq727008 X0 X1 X3
       have i₂ := eq727008 X2 X1 X3
       grind)
    | (have i₁ := eq727008 X0 X1 X0
       have i₂ := eq727008 X0 X1 X2
       grind)
    | exact superpose eq727008 eq727008
    | (have j0 := eq727008 X0 X1 X2
       have j1 := eq727008 X0 X1 X2
       grind)
    | exact resolve eq727008 eq727008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727008
  have eq746285 : ∀ X0 X1 X2 X3 : G, (τ (M.op X0 (M.op X0 X1))) = (τ (M.op X2 (M.op X2 X1))) ∨ X1 = X3 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq746277 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746277
  have eq808222 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq207710 y
       have i₂ := eq275929
       grind)
    | exact superpose eq275929 eq207710
    | exact resolve eq207710 eq275929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207710 eq275929
  have eq808243 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq808222
       grind)
    | exact superpose eq808222 eq14
    | exact resolve eq14 eq808222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808222
  have eq808269 : (σ x) ≠ (σ x) ∨ x = y ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq808243
       have i₂ := eq259413
       grind)
    | exact superpose eq259413 eq808243
    | (have r₁ := eq808243
       have r₂ := eq259413
       grind)
    | exact resolve eq808243 eq259413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259413 eq808243
  have eq808274 : (σ x) ≠ (σ x) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq808269
  have eq808275 : y = (M.op x x) ∨ x = y := by grind
  clear eq808274
  have eq808536 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (σ y))) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq442170 x x
       have i₂ := eq808275
       grind)
    | exact superpose eq808275 eq442170
    | exact resolve eq442170 eq808275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442170
  have eq808570 : ∀ X0 : G, (M.op y (M.op X0 x)) = (M.op X0 y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq95 x x x
       have i₂ := eq808275
       grind)
    | exact superpose eq808275 eq95
    | exact resolve eq95 eq808275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq808578 : y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq437 x x
       have i₂ := eq808275
       grind)
    | exact superpose eq808275 eq437
    | exact resolve eq437 eq808275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437 eq808275
  have eq808847 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (σ y))) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq808536 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808536
  have eq809418 : ∀ X0 : G, x = (M.op (M.op X0 x) (k y y)) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq277206 y x X0
       have i₂ := eq808578
       grind)
    | exact superpose eq808578 eq277206
    | (have j0 := eq277206 x (M.op (M.op X0 x) (k y y)) x
       grind)
    | exact resolve eq277206 eq808578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277206
  have eq809508 : ∀ X0 : G, x = (M.op (M.op X0 x) (k y y)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq809418 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809418
  have eq818142 : (σ (M.op x y)) = (σ (M.op x (M.op y x))) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq745508 x y
       have i₂ := eq808570 x
       grind)
    | exact superpose eq808570 eq745508
    | (have j0 := eq745508 (σ (M.op x y)) (σ (M.op x (M.op y x)))
       grind)
    | exact resolve eq745508 eq808570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745508 eq808570
  have eq818293 : (σ (M.op x y)) = (σ (M.op x (M.op y x))) ∨ x = y := by grind
  clear eq818142
  have eq824731 : ∀ X0 X2 : G, (τ (σ x)) = (τ (M.op X0 (M.op X0 (σ y)))) ∨ (σ y) = X2 ∨ x = y := by
    intro X0 X2
    first
    | (have i₁ := eq746285 X0 (σ y) x X2
       have i₂ := eq808847 x
       grind)
    | exact superpose eq808847 eq746285
    | (have j0 := eq746285 X0 (τ (σ x)) X2 (τ (M.op X0 (M.op X0 (σ y))))
       grind)
    | exact resolve eq746285 eq808847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746285
  have eq824742 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq3102 (σ y) x x
       have i₂ := eq808847 x
       grind)
    | exact superpose eq808847 eq3102
    | exact resolve eq3102 eq808847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3102
  have eq824781 : ∀ X0 : G, (σ x) = (k (σ x) (M.op (M.op X0 (σ y)) (σ x))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1114 (M.op X0 (σ y)) X0
       have i₂ := eq808847 X0
       grind)
    | exact superpose eq808847 eq1114
    | exact resolve eq1114 eq808847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114 eq808847
  have eq824846 : ∀ X0 X2 : G, x = (τ (M.op X0 (M.op X0 (σ y)))) ∨ (σ y) = X2 ∨ x = y := by
    intro X0 X2
    first
    | (have i₁ := eq824731 X0 X2
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq824731
    | (have j0 := eq824731 X0 X2
       grind)
    | exact resolve eq824731 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824731
  have eq828443 : x = (M.op y (k y y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq809508 y
       have i₂ := eq808578
       grind)
    | exact superpose eq808578 eq809508
    | exact resolve eq809508 eq808578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808578 eq809508
  have eq828565 : x = (M.op y (k y y)) ∨ x = y := by grind
  clear eq828443
  have eq828758 : ∀ X0 X1 : G, (k y y) = (M.op y (M.op X0 (M.op X1 (M.op X1 (M.op X0 x))))) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq20402 X0 X1 y (k y y)
       have i₂ := eq828565
       grind)
    | exact superpose eq828565 eq20402
    | exact resolve eq20402 eq828565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828565
  have eq828823 : (M.op x (M.op y x)) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq828758 x x
       have i₂ := eq20269 x x x y
       grind)
    | exact superpose eq20269 eq828758
    | exact resolve eq828758 eq20269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20269 eq828758
  have eq868987 : (σ (M.op x y)) = (σ (k y y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq818293
       have i₂ := eq828823
       grind)
    | exact superpose eq828823 eq818293
    | exact resolve eq818293 eq828823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818293 eq828823
  have eq868997 : (σ (M.op x y)) = (σ (k y y)) ∨ x = y := by grind
  clear eq868987
  have eq1060934 : ∀ X0 : G, (τ (σ x)) = (k x (τ (M.op (M.op X0 (σ y)) (σ x)))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq33 x (M.op (M.op X0 (σ y)) (σ x))
       have i₂ := eq824781 X0
       grind)
    | exact superpose eq824781 eq33
    | exact resolve eq33 eq824781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq824781
  have eq1060937 : ∀ X0 : G, x = (k x (τ (M.op (M.op X0 (σ y)) (σ x)))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1060934 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq1060934
    | exact resolve eq1060934 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060934
  have eq1061265 : ∀ X0 X1 : G, (τ (σ y)) = X0 ∨ x = (τ (M.op X1 (M.op X1 (σ y)))) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0
       have i₂ := eq824846 X1 (σ X0)
       grind)
    | (have i₁ := eq9 y
       have i₂ := eq824846 X0 x
       grind)
    | exact superpose eq824846 eq9
    | (have j1 := eq824846 X1 x
       grind)
    | exact resolve eq9 eq824846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824846
  have eq1061314 : ∀ X0 X1 : G, x = (τ (M.op X1 (M.op X1 (σ y)))) ∨ y = X0 ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq1061265 X0 X1
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1061265
    | (have j0 := eq1061265 X0 X1
       grind)
    | exact resolve eq1061265 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061265
  have eq1061772 : ∀ X1 : G, x = y ∨ x = y ∨ x = (τ (M.op X1 (M.op X1 (σ y)))) ∨ x = y := by
    intro X1
    first
    | (have i₁ := eq1060937 x
       have i₂ := eq1061314 (k x (τ (M.op (M.op x (σ y)) (σ x)))) X1
       grind)
    | exact superpose eq1061314 eq1060937
    | (have j1 := eq1061314 x X1
       grind)
    | exact resolve eq1060937 eq1061314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060937 eq1061314
  have eq1061775 : ∀ X1 : G, x = (τ (M.op X1 (M.op X1 (σ y)))) ∨ x = y := by
    intro X1
    first
    | (have j0 := eq1061772 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061772
  have eq1062077 : ∀ X0 : G, (τ (σ X0)) = x ∨ x = y ∨ (M.op (σ X0) (σ y)) = (σ (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq1061775 (σ y)
       have i₂ := eq213307 X0 y
       grind)
    | exact superpose eq213307 eq1061775
    | (have j1 := eq213307 X0 y
       grind)
    | exact resolve eq1061775 eq213307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213307 eq1061775
  have eq1062147 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k X0 y)) ∨ x = y ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq1062077 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1062077
    | (have j0 := eq1062077 X0
       grind)
    | exact resolve eq1062077 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062077
  have eq1179970 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ (k y y)))) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq168 X0 (σ y)
       have i₂ := eq1062147 y
       grind)
    | exact superpose eq1062147 eq168
    | (have j1 := eq1062147 y
       grind)
    | exact resolve eq168 eq1062147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168 eq1062147
  have eq1179977 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ (k y y)))) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq1179970 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179970
  have eq1180105 : ∀ X0 X1 : G, (σ (k y y)) = (M.op X0 (M.op X0 (M.op X1 (M.op X1 (σ y))))) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq20402 X0 X1 X0 (σ (k y y))
       have i₂ := eq1179977 X0
       grind)
    | exact superpose eq1179977 eq20402
    | exact resolve eq20402 eq1179977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20402 eq1179977
  have eq1180116 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ x = y := by
    first
    | (have i₁ := eq1180105 x x
       have i₂ := eq2020 x (σ y) x
       grind)
    | exact superpose eq2020 eq1180105
    | exact resolve eq1180105 eq2020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2020 eq1180105
  have eq1180130 : (M.op (σ x) (σ y)) = (σ (k y y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq824742
       have i₂ := eq1180116
       grind)
    | exact superpose eq1180116 eq824742
    | exact resolve eq824742 eq1180116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824742 eq1180116
  have eq1180178 : (M.op (σ x) (σ y)) = (σ (k y y)) ∨ x = y := by grind
  clear eq1180130
  have eq1180558 : (σ (M.op x y)) ≠ (σ (k y y)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq1180178
       grind)
    | exact superpose eq1180178 eq14
    | exact resolve eq14 eq1180178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180178
  have eq1180628 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq1180558
       have i₂ := eq868997
       grind)
    | exact superpose eq868997 eq1180558
    | (have r₁ := eq1180558
       have r₂ := eq868997
       grind)
    | exact resolve eq1180558 eq868997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868997 eq1180558
  have eq1180643 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by grind
  clear eq1180628
  have eq1180644 : x = y := by grind
  clear eq1180643
  have eq1180656 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1180644
       grind)
    | exact superpose eq1180644 eq14
    | exact resolve eq14 eq1180644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1180990 : x = (k x x) := by
    first
    | (have i₁ := eq211092
       have i₂ := eq1180644
       grind)
    | exact superpose eq1180644 eq211092
    | exact resolve eq211092 eq1180644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211092
  have eq1181566 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq727422
       have i₂ := eq1180644
       grind)
    | exact superpose eq1180644 eq727422
    | exact resolve eq727422 eq1180644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727422 eq1180644
  have eq1181859 : (σ x) = (σ (M.op x x)) := by grind
  clear eq1181566
  have eq1182127 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1180656
       have i₂ := eq1181859
       grind)
    | exact superpose eq1181859 eq1180656
    | exact resolve eq1180656 eq1181859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180656 eq1181859
  have eq1182794 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq56 x
       have i₂ := eq1180990
       grind)
    | exact superpose eq1180990 eq56
    | (have j0 := eq56 x
       grind)
    | exact resolve eq56 eq1180990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq1180990
  have eq1182867 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1182794
  have eq1188116 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1182127
       have i₂ := eq1182867
       grind)
    | exact superpose eq1182867 eq1182127
    | (have r₁ := eq1182127
       have r₂ := eq1182867
       grind)
    | exact resolve eq1182127 eq1182867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182127 eq1182867
  have eq1188476 : False := by grind
  exact eq1188476
