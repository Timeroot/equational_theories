import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_x_pyx_pxy_Equation434 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq21 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq8 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq8 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (M.op X1 X0) X0
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq21
    | exact resolve eq21 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op (M.op X1 X0) X0) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X1 X0)
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq11
    | (have j0 := eq11 X0 (M.op X1 X0)
       grind)
    | (have r₁ := eq11 X0 (M.op X1 X0)
       have r₂ := eq21 X0 X1
       grind)
    | exact resolve eq11 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq32 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X1
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq30
    | exact resolve eq30 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq39 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op (M.op X1 X1) X0) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X1 X1)
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq11
    | (have j0 := eq11 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq11 X1 (M.op X0 X0)
       have r₂ := eq22 X0 X1
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (M.op X1 X1) X0
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq21
    | exact resolve eq21 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq42 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 X1
       have i₂ := eq40 X0 X1
       grind)
    | (have i₁ := eq41 (M.op X1 X1) X1
       have i₂ := eq40 X0 (M.op X1 X1)
       grind)
    | exact superpose eq40 eq41
    | exact resolve eq41 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq41
  have eq44 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k (M.op X0 X1) X1) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X1) X1
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq11
    | (have j0 := eq11 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq11 (M.op X1 X0) X0
       have r₂ := eq24 X0 X1
       grind)
    | exact resolve eq11 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq54 : ∀ X0 X1 : G, (k (M.op X0 X1) X1) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq55 : ∀ X0 X1 : G, (k (M.op X0 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X1
       have i₂ := eq21 X1 X0
       grind)
    | exact superpose eq21 eq54
    | exact resolve eq54 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq57 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
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
  have eq80 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq44 x y
       grind)
    | exact superpose eq44 eq14
    | (have j1 := eq44 x y
       grind)
    | exact resolve eq14 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (M.op X1 (σ (k X0 X0))) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X0) X1
       have i₂ := eq44 X0 X0
       grind)
    | exact superpose eq44 eq22
    | (have j1 := eq44 X0 X0
       grind)
    | exact resolve eq22 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (σ X1) (σ X0)
       have i₂ := eq44 X0 X1
       grind)
    | exact superpose eq44 eq21
    | (have j1 := eq44 X1 (k X0 X1)
       grind)
    | exact resolve eq21 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq95 : ∀ X0 X1 : G, (k (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq32 (M.op X0 X0) X1
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq32
    | exact resolve eq32 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq122 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X1 X1)
       have i₂ := eq95 (τ X0) X1
       grind)
    | exact superpose eq95 eq16
    | exact resolve eq16 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq123 : ∀ X0 X1 : G, (k (σ (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq122 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq122
    | exact resolve eq122 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq137 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (σ (M.op X1 X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (σ (M.op X1 X1))
       have i₂ := eq123 (τ X0) X1
       grind)
    | exact superpose eq123 eq16
    | exact resolve eq16 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq138 : ∀ X0 X1 : G, (k (σ (σ (M.op X1 X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq137 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq137
    | exact resolve eq137 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq139 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq141 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ X1))) = (τ (k X2 (k (σ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X2 (k X0 (τ X1))
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq20
    | exact resolve eq20 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 (σ X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (M.op X1 (σ X0)) X0
       have i₂ := eq55 X1 (σ X0)
       grind)
    | exact superpose eq55 eq20
    | exact resolve eq20 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 X1 : G, (k (τ (M.op X1 (σ X0))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq145 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq145
    | exact resolve eq145 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq246 : ∀ X0 X1 : G, (k (τ (σ (k X0 X1))) X1) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq151 X1 (σ X0)
       have i₂ := eq44 X0 X1
       grind)
    | exact superpose eq44 eq151
    | (have j1 := eq44 X0 X1
       grind)
    | exact resolve eq151 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq258 : ∀ X0 X1 : G, (k (k X0 X1) X1) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq246 X0 X1
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq246
    | (have j0 := eq246 X0 X1
       grind)
    | exact resolve eq246 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq503 : ∀ X0 X1 X2 : G, (τ (k X2 (k (σ X0) X1))) = (k (τ X2) (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X2 (M.op X0 (τ X1))
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq20
    | (have j1 := eq57 X0 X1
       grind)
    | exact resolve eq20 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq513 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ X1))) = (k (τ X2) (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq503 X0 X1 X2
       have i₂ := eq141 X0 X1 X2
       grind)
    | exact superpose eq141 eq503
    | (have j0 := eq503 X0 X1 X2
       grind)
    | exact resolve eq503 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq503
  have eq568 : ∀ X0 X1 : G, (M.op X1 (k (σ (τ X0)) X0)) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq81 (τ X0) X1
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq81
    | (have j0 := eq81 (τ X0) X1
       grind)
    | exact resolve eq81 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq81
  have eq590 : ∀ X0 X1 : G, (M.op X1 (k X0 X0)) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq568 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq568
    | (have j0 := eq568 X0 X1
       grind)
    | exact resolve eq568 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq595 : ∀ X0 X1 : G, (M.op X1 (k X0 X0)) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq590 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq590
    | (have j0 := eq590 X0 X1
       grind)
    | exact resolve eq590 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq703 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq80
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq80
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq80 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq704 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq703
  have eq851 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ (k X0 X1)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq86 (τ X0) (τ X1)
       have i₂ := eq139 X1 X0
       grind)
    | exact superpose eq139 eq86
    | (have j0 := eq86 (τ X1) (τ (k X0 X1))
       grind)
    | exact resolve eq86 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq870 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq851 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq851
    | (have j0 := eq851 X0 X1
       grind)
    | exact resolve eq851 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq878 : ∀ X0 X1 : G, (M.op X1 (k X0 X1)) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq870 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq870
    | (have j0 := eq870 X0 X1
       grind)
    | exact resolve eq870 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq879 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X1 (k X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq878 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq878
    | (have j0 := eq878 X0 X1
       grind)
    | exact resolve eq878 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878
  have eq880 : ∀ X0 X1 : G, (M.op X1 (k X0 X1)) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq879 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq879
    | (have j0 := eq879 X0 X1
       grind)
    | exact resolve eq879 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879
  have eq1509 : ∀ X0 X1 : G, (k X1 X1) = (k X0 (k X1 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 (k X1 X1)
       have i₂ := eq595 X1 X0
       grind)
    | exact superpose eq595 eq55
    | (have j1 := eq595 X1 X1
       grind)
    | exact resolve eq55 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq1922 : y = (k (τ (σ x)) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq151 y (σ x)
       have i₂ := eq704
       grind)
    | exact superpose eq704 eq151
    | exact resolve eq151 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq704
  have eq1932 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1922
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq1922
    | exact resolve eq1922 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1922
  have eq2063 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq880 x y
       have i₂ := eq1932
       grind)
    | exact superpose eq1932 eq880
    | (have j0 := eq880 y y
       grind)
    | exact resolve eq880 eq1932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880 eq1932
  have eq2064 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq2063
  have eq2193 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq22 y X0
       have i₂ := eq2064
       grind)
    | exact superpose eq2064 eq22
    | exact resolve eq22 eq2064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2064
  have eq2469 : x ≠ x ∨ x = (M.op x y) := by
    first
    | (have j0 := eq2193 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2193
  have eq2470 : x = (M.op x y) := by grind
  clear eq2469
  have eq2574 : y = (k x y) := by
    first
    | (have i₁ := eq55 x y
       have i₂ := eq2470
       grind)
    | exact superpose eq2470 eq55
    | exact resolve eq55 eq2470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq11841 : ∀ X0 X1 : G, (k (τ X1) (τ X1)) = (k (τ X0) (M.op (τ X1) (τ X1))) ∨ (τ X1) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1509 (τ X0) (τ X1)
       have i₂ := eq513 (τ X1) X1 X0
       grind)
    | exact superpose eq513 eq1509
    | (have j0 := eq1509 X0 (τ X1)
       have j1 := eq513 (τ X1) X1 x
       grind)
    | exact resolve eq1509 eq513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513 eq1509
  have eq11912 : ∀ X0 X1 : G, (k (τ X1) (τ X1)) = (k (τ X0) (M.op (τ X1) (τ X1))) ∨ (τ X1) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq11841 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11841
  have eq11930 : ∀ X1 : G, (k (τ X1) (τ X1)) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X1)) := by
    intro X1
    first
    | (have i₁ := eq11912 x X1
       have i₂ := eq42 (τ x) (τ X1)
       grind)
    | exact superpose eq42 eq11912
    | (have j0 := eq11912 x X1
       grind)
    | exact resolve eq11912 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq11912
  have eq11947 : ∀ X1 : G, (k (τ X1) (τ X1)) = (M.op (τ X1) (τ X1)) := by
    intro X1
    first
    | (have j0 := eq11930 X1
       have j1 := eq11 (τ X1) (τ X1)
       grind)
    | (have r₁ := eq11930 X1
       have r₂ := eq11 (τ X1) (τ X1)
       grind)
    | exact resolve eq11930 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11930
  have eq11962 : ∀ X1 : G, (τ (k X1 X1)) = (M.op (τ X1) (τ X1)) := by
    intro X1
    first
    | (have i₁ := eq11947 X1
       have i₂ := eq139 X1 X1
       grind)
    | exact superpose eq139 eq11947
    | exact resolve eq11947 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq11947
  have eq12127 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq11962 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq11962
    | exact resolve eq11962 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12143 : ∀ X0 X1 : G, (M.op X1 (τ (k X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22 (τ X0) X1
       have i₂ := eq11962 X0
       grind)
    | exact superpose eq11962 eq22
    | exact resolve eq22 eq11962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11962
  have eq12195 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq12127 X0
       have i₂ := eq20 (σ X0) X0
       grind)
    | exact superpose eq20 eq12127
    | exact resolve eq12127 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq12127
  have eq12202 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq12195 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq12195
    | exact resolve eq12195 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12195
  have eq13589 : ∀ X0 X1 : G, (M.op X1 (τ (σ (σ (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12143 (σ (σ (M.op X0 X0))) X1
       have i₂ := eq138 (σ (σ (M.op X0 X0))) X0
       grind)
    | exact superpose eq138 eq12143
    | exact resolve eq12143 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq12143
  have eq13674 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13589 X0 X1
       have i₂ := eq9 (σ (M.op X0 X0))
       grind)
    | exact superpose eq9 eq13589
    | exact resolve eq13589 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13589
  have eq60213 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq258 x y
       have i₂ := eq2574
       grind)
    | exact superpose eq2574 eq258
    | (have j0 := eq258 x y
       grind)
    | exact resolve eq258 eq2574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258 eq2574
  have eq60458 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq60213
       have i₂ := eq12202 y
       grind)
    | exact superpose eq12202 eq60213
    | exact resolve eq60213 eq12202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12202 eq60213
  have eq62477 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq60458
       grind)
    | exact superpose eq60458 eq14
    | exact resolve eq14 eq60458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60458
  have eq62494 : (σ x) ≠ (σ x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq62477
       have i₂ := eq2470
       grind)
    | exact superpose eq2470 eq62477
    | exact resolve eq62477 eq2470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2470 eq62477
  have eq62495 : y = (M.op y y) := by grind
  clear eq62494
  have eq62855 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq22 y X0
       have i₂ := eq62495
       grind)
    | exact superpose eq62495 eq22
    | exact resolve eq22 eq62495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq62892 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq13674 y X0
       have i₂ := eq62495
       grind)
    | exact superpose eq62495 eq13674
    | exact resolve eq13674 eq62495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13674 eq62495
  have eq69604 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq62892 (σ x)
       grind)
    | exact superpose eq62892 eq14
    | exact resolve eq14 eq62892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62892
  have eq69606 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq69604
       have i₂ := eq62855 x
       grind)
    | exact superpose eq62855 eq69604
    | exact resolve eq69604 eq62855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62855 eq69604
  have eq69607 : False := by grind
  exact eq69607

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pxx_pxy_Equation434 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq22 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq8 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X0 X0)
       have i₂ := eq22 X0 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq11
    | (have j0 := eq11 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq22 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq37 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq12 X2 X0
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X1 X0
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq44 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq37 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq61 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq16
  have eq102 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq218 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (σ X0) X1
       have i₂ := eq42 X2 X0
       grind)
    | exact superpose eq42 eq22
    | (have j1 := eq42 X2 X0
       grind)
    | exact resolve eq22 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq269 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 (M.op X1 X1)
       have i₂ := eq34 X1 (σ X0)
       grind)
    | exact superpose eq34 eq61
    | exact resolve eq61 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) ≠ (k X0 (M.op X1 X1)) ∨ (k X0 (M.op X1 X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq102 X1 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq102
    | exact resolve eq102 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq575 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq102 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq579 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq560 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq603 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq575 (σ X0)
       grind)
    | exact superpose eq575 eq13
    | exact resolve eq13 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq621 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq603 X0
       have i₂ := eq575 X0
       grind)
    | exact superpose eq575 eq603
    | exact resolve eq603 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq756 : ∀ X0 X1 : G, (τ (k (σ X0) (M.op X1 X1))) = (k (τ (σ X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ X0) X0
       have i₂ := eq579 (σ X0) X1
       grind)
    | exact superpose eq579 eq20
    | exact resolve eq20 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq579
  have eq760 : ∀ X0 X1 : G, (k X0 X0) = (τ (k (σ X0) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq756 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq756
    | exact resolve eq756 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756
  have eq781 : ∀ X0 X1 : G, (k X0 X0) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq760 X0 X1
       have i₂ := eq61 X0 (M.op X1 X1)
       grind)
    | exact superpose eq61 eq760
    | exact resolve eq760 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq760
  have eq970 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq43
    | (have j0 := eq43 X0 X1
       grind)
    | exact resolve eq43 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq1045 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq970 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq970
    | (have j0 := eq970 X0 X1
       grind)
    | exact resolve eq970 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970
  have eq1316 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X0) X1
       have i₂ := eq621 X0
       grind)
    | exact superpose eq621 eq22
    | exact resolve eq22 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq1888 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq218 y X0 x
       grind)
    | exact superpose eq218 eq14
    | (have j1 := eq218 y X0 x
       grind)
    | exact resolve eq14 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq34307 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 (σ y)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq1888 X0
       have i₂ := eq1045 x y
       grind)
    | exact superpose eq1045 eq1888
    | (have j0 := eq1888 X0
       have j1 := eq1045 X0 y
       grind)
    | (have r₁ := eq1888 X0
       have r₂ := eq1045 x y
       grind)
    | exact resolve eq1888 eq1045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045 eq1888
  have eq34308 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq34307 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34307
  have eq34418 : ∀ X0 : G, (τ (σ y)) = (k y (τ (M.op X0 X0))) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq269 y X0
       have i₂ := eq34308 (σ y)
       grind)
    | exact superpose eq34308 eq269
    | exact resolve eq269 eq34308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq34308
  have eq34439 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq34418 x
       have i₂ := eq781 y x
       grind)
    | exact superpose eq781 eq34418
    | exact resolve eq34418 eq781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781 eq34418
  have eq34476 : (τ (σ y)) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq34439
       have i₂ := eq575 y
       grind)
    | exact superpose eq575 eq34439
    | exact resolve eq34439 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575 eq34439
  have eq34488 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq34476
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq34476
    | exact resolve eq34476 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34476
  have eq34489 : y = (M.op y y) := by grind
  clear eq34488
  have eq34656 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq22 y X0
       have i₂ := eq34489
       grind)
    | exact superpose eq34489 eq22
    | exact resolve eq22 eq34489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq34705 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1316 y X0
       have i₂ := eq34489
       grind)
    | exact superpose eq34489 eq1316
    | exact resolve eq1316 eq34489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1316 eq34489
  have eq38564 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq34705 (σ x)
       grind)
    | exact superpose eq34705 eq14
    | exact resolve eq14 eq34705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34705
  have eq38587 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq38564
       have i₂ := eq34656 x
       grind)
    | exact superpose eq34656 eq38564
    | exact resolve eq38564 eq34656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34656 eq38564
  have eq38588 : False := by grind
  exact eq38588

/-- `Equation436`: `x = x ◇ (y ◇ (y ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation436 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law436 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law436.models_iff G M).mp hM
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
  have eq48 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq88 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq92 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq88 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq88 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq88 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq88 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq108 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq92 (σ X0) (σ X1)
       grind)
    | exact superpose eq92 eq13
    | exact resolve eq13 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq108 X0 X1
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq108
    | exact resolve eq108 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq108
  have eq1449 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq115 x y
       grind)
    | exact superpose eq115 eq14
    | (have r₁ := eq14
       have r₂ := eq115 x y
       grind)
    | exact resolve eq14 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq1469 : False := by grind
  exact eq1469

/-- `Equation4385`: `x ◇ (x ◇ x) = (y ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pyx_Equation4385 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4385 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4385.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq18 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X2 X1) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq8 X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq8 X0 (M.op x X0)
       have i₂ := eq8 X0 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq30 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0 (M.op x X0)
       have i₂ := eq8 X0 x
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq61 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24
    | exact resolve eq24 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 X0
       have i₂ := eq12 X1 (σ X0)
       grind)
    | exact superpose eq12 eq24
    | (have j1 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq24 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq76 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq82 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq38
  have eq103 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq76 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq19 X0
       grind)
    | exact superpose eq19 eq76
    | (have j0 := eq76 X0 (M.op X0 (M.op X0 X0))
       grind)
    | (have r₁ := eq76 X0 (M.op X0 (M.op X0 X0))
       have r₂ := eq19 X0
       grind)
    | exact resolve eq76 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq104 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq103 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq170 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq53 X0 X1
       have i₂ := eq12 X0 (M.op X1 X0)
       grind)
    | exact superpose eq12 eq53
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq53 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (k X1 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq104 X0
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq104
    | exact resolve eq104 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq30 X1 X0
       grind)
    | exact superpose eq30 eq9
    | (have j1 := eq30 X1 X0
       grind)
    | exact resolve eq9 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq283 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (σ X1) (M.op (σ X0) (σ X0))) ∨ (M.op (σ X2) (σ X0)) = (σ (k X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq30 X2 X0
       grind)
    | exact superpose eq30 eq13
    | (have j1 := eq30 X2 X0
       grind)
    | exact resolve eq13 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq619 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq33
    | exact resolve eq33 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq683 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq619 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq619
    | (have j0 := eq619 X0 X1
       grind)
    | exact resolve eq619 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq734 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq1569 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq82 X1
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq82
    | (have j1 := eq30 X0 X1
       grind)
    | exact resolve eq82 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq82
  have eq1610 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1569 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1569
    | (have j0 := eq1569 X0 X1
       grind)
    | exact resolve eq1569 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1569
  have eq2070 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (M.op (σ X2) (σ X1)) = (σ (k X1 X2)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq281 X1 X2
       have i₂ := eq281 X1 X0
       grind)
    | (have i₁ := eq281 X0 X1
       have i₂ := eq281 X0 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact superpose eq281 eq281
    | (have j0 := eq281 X1 X2
       have j1 := eq281 X1 X2
       grind)
    | exact resolve eq281 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2089 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq281 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq281
    | exact resolve eq281 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2143 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2089 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq2089
    | (have j0 := eq2089 X0 X1
       grind)
    | exact resolve eq2089 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq2089
  have eq2155 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2143 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2143
    | (have j0 := eq2143 X1 (τ X0)
       grind)
    | exact resolve eq2143 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2143
  have eq2703 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1610 x y
       grind)
    | exact superpose eq1610 eq14
    | (have j1 := eq1610 x y
       grind)
    | exact resolve eq14 eq1610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2749 : x = (k y x) := by
    first
    | (have j1 := eq734 x y
       grind)
    | (have r₁ := eq2703
       have r₂ := eq734 x y
       grind)
    | exact resolve eq2703 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2703
  have eq2892 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq683 x y
       have i₂ := eq2749
       grind)
    | exact superpose eq2749 eq683
    | (have j0 := eq683 x y
       grind)
    | exact resolve eq683 eq2749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8911 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    grind
  clear eq283
  have eq14269 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq64 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq64
    | exact resolve eq64 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq14611 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14269 X0 X1
       have i₂ := eq61 X0 X1
       grind)
    | exact superpose eq61 eq14269
    | (have j0 := eq14269 X0 X1
       grind)
    | exact resolve eq14269 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14269
  have eq59249 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8911 (τ X1) (τ X0)
       have i₂ := eq61 X0 X1
       grind)
    | exact superpose eq61 eq8911
    | exact resolve eq8911 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59661 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 X1)
       have i₂ := eq8911 X0 X1
       grind)
    | exact superpose eq8911 eq9
    | (have j1 := eq8911 X0 X1
       grind)
    | exact resolve eq9 eq8911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60035 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq8911 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8911
  have eq60036 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq60035 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60035
  have eq60339 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (k X0 X0))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq59661 X0 X1
       have i₂ := eq60036 X0
       grind)
    | exact superpose eq60036 eq59661
    | (have j0 := eq59661 X0 X1
       grind)
    | exact resolve eq59661 eq60036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59661
  have eq60623 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (k (τ X0) (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq59249 X0 X1
       have i₂ := eq60036 (τ X0)
       grind)
    | exact superpose eq60036 eq59249
    | (have j0 := eq59249 X0 X1
       grind)
    | exact resolve eq59249 eq60036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59249
  have eq60862 : ∀ X0 X1 : G, (k X0 X1) = (k X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq60339 X0 X1
       have i₂ := eq9 (k X0 X0)
       grind)
    | exact superpose eq9 eq60339
    | (have j0 := eq60339 X0 X1
       grind)
    | exact resolve eq60339 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60339
  have eq60982 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (k (σ (τ X0)) X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq60623 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq60623
    | (have j0 := eq60623 X0 X1
       grind)
    | exact resolve eq60623 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60623
  have eq61157 : ∀ X0 X1 : G, (k X0 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq60982 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq60982
    | (have j0 := eq60982 X0 X1
       grind)
    | exact resolve eq60982 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60982
  have eq61240 : ∀ X0 X1 : G, (k X0 X1) = (k X0 X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq61157 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq61157
    | (have j0 := eq61157 X0 X1
       grind)
    | exact resolve eq61157 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61157
  have eq61281 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq61240 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq61240
    | (have j0 := eq61240 X0 X1
       grind)
    | exact resolve eq61240 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61240
  have eq61300 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq61281 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq61281
    | (have j0 := eq61281 X0 X1
       grind)
    | exact resolve eq61281 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61281
  have eq61305 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq61300 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq61300
    | (have j0 := eq61300 X0 X1
       grind)
    | exact resolve eq61300 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61300
  have eq61347 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq60036 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq60036
    | exact resolve eq60036 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61427 : ∀ X0 X1 : G, (τ (σ (k X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq281 X0 X1
       have i₂ := eq60036 X0
       grind)
    | exact superpose eq60036 eq281
    | (have j0 := eq281 X0 X1
       grind)
    | exact resolve eq281 eq60036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq61449 : ∀ X0 X1 : G, (M.op (σ X0) (σ (k X0 X0))) = (M.op (M.op X1 (σ X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X0) X1
       have i₂ := eq60036 X0
       grind)
    | exact superpose eq60036 eq8
    | exact resolve eq8 eq60036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61476 : ∀ X0 X1 : G, (τ X1) = (τ (σ (k X0 X0))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2155 X1 (σ X0)
       have i₂ := eq60036 X0
       grind)
    | exact superpose eq60036 eq2155
    | (have j0 := eq2155 X1 (σ X0)
       grind)
    | exact resolve eq2155 eq60036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2155
  have eq61494 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq8 (σ X0) (σ X0)
       have i₂ := eq60036 X0
       grind)
    | exact superpose eq60036 eq8
    | exact resolve eq8 eq60036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61556 : ∀ X0 X1 : G, (τ X1) = (k X0 X0) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq61476 X0 X1
       have i₂ := eq9 (k X0 X0)
       grind)
    | exact superpose eq9 eq61476
    | (have j0 := eq61476 X0 X1
       grind)
    | exact resolve eq61476 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61476
  have eq61577 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq61427 X0 X1
       have i₂ := eq9 (k X0 X0)
       grind)
    | exact superpose eq9 eq61427
    | (have j0 := eq61427 X0 X1
       grind)
    | exact resolve eq61427 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61427
  have eq61620 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq61347 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq61347
    | exact resolve eq61347 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq61347
  have eq61663 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq61620 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq61620
    | exact resolve eq61620 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61620
  have eq63339 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq61 X0 X0
       have i₂ := eq61663 (τ X0)
       grind)
    | exact superpose eq61663 eq61
    | exact resolve eq61 eq61663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq63391 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq63339 X0
       have i₂ := eq61663 X0
       grind)
    | exact superpose eq61663 eq63339
    | exact resolve eq63339 eq61663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63339
  have eq78681 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq61663 X0
       have i₂ := eq61305 X0 X1
       grind)
    | (have i₁ := eq61663 X1
       have i₂ := eq61305 X1 X1
       grind)
    | exact superpose eq61305 eq61663
    | (have j1 := eq61305 X0 X1
       grind)
    | exact resolve eq61663 eq61305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78795 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq61305 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78796 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq61305 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61305
  have eq78797 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq78796 X0 X1
       have i₂ := eq61663 X0
       grind)
    | exact superpose eq61663 eq78796
    | (have j0 := eq78796 X0 X1
       grind)
    | (have r₁ := eq78796 X0 X0
       have r₂ := eq61663 X0
       grind)
    | exact resolve eq78796 eq61663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78796
  have eq78798 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq78795 X0 X1
       have i₂ := eq61663 X0
       grind)
    | exact superpose eq61663 eq78795
    | (have j0 := eq78795 X0 X1
       grind)
    | (have r₁ := eq78795 X0 X0
       have r₂ := eq61663 X0
       grind)
    | exact resolve eq78795 eq61663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78795
  have eq79155 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq78798 X0 X1
       have i₂ := eq61663 X0
       grind)
    | exact superpose eq61663 eq78798
    | (have j0 := eq78798 X0 X1
       grind)
    | exact resolve eq78798 eq61663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78798
  have eq87714 : ∀ X0 X1 : G, (M.op (M.op X1 (σ X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq61449 X0 X1
       have i₂ := eq61663 X0
       grind)
    | exact superpose eq61663 eq61449
    | exact resolve eq61449 eq61663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61449
  have eq88129 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq61494 X0
       have i₂ := eq61663 X0
       grind)
    | exact superpose eq61663 eq61494
    | exact resolve eq61494 eq61663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61494
  have eq88916 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (τ (σ X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq61556 X1 (σ X0)
       grind)
    | exact superpose eq61556 eq13
    | (have j1 := eq61556 X1 (σ X0)
       grind)
    | exact resolve eq13 eq61556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61556
  have eq88958 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq88916 X0 X1
       have i₂ := eq61663 X1
       grind)
    | exact superpose eq61663 eq88916
    | (have j0 := eq88916 X0 X1
       grind)
    | exact resolve eq88916 eq61663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88916
  have eq89077 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq88958 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq88958
    | (have j0 := eq88958 X0 X1
       grind)
    | exact resolve eq88958 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88958
  have eq89277 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq61577 y x
       grind)
    | exact superpose eq61577 eq14
    | (have j1 := eq61577 y x
       grind)
    | exact resolve eq14 eq61577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61577
  have eq89389 : (σ (M.op x y)) ≠ (σ x) ∨ x = (k y y) := by
    first
    | (have i₁ := eq89277
       have i₂ := eq2749
       grind)
    | exact superpose eq2749 eq89277
    | exact resolve eq89277 eq2749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2749 eq89277
  have eq89452 : x = (M.op y y) ∨ (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq89389
       have i₂ := eq61663 y
       grind)
    | exact superpose eq61663 eq89389
    | exact resolve eq89389 eq61663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89389
  have eq89488 : x = (M.op y y) := by
    first
    | (have r₁ := eq89452
       have r₂ := eq2892
       grind)
    | exact resolve eq89452 eq2892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2892 eq89452
  have eq89560 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq8 y y
       have i₂ := eq89488
       grind)
    | exact superpose eq89488 eq8
    | exact resolve eq8 eq89488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89566 : (M.op x y) = (M.op (M.op y x) y) := by
    first
    | (have i₁ := eq53 y y
       have i₂ := eq89488
       grind)
    | exact superpose eq89488 eq53
    | exact resolve eq53 eq89488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq89584 : (M.op x y) = (k y (M.op x y)) := by
    first
    | (have i₁ := eq230 y y
       have i₂ := eq89488
       grind)
    | exact superpose eq89488 eq230
    | exact resolve eq230 eq89488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq89725 : (M.op x y) ≠ (M.op x x) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq79155 x y
       have i₂ := eq89560
       grind)
    | exact superpose eq89560 eq79155
    | (have j0 := eq79155 x y
       grind)
    | exact resolve eq79155 eq89560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89843 : (M.op y (M.op y x)) = (M.op (M.op x y) (M.op y x)) ∨ (M.op y (M.op y x)) = (k (M.op y x) y) := by
    first
    | (have i₁ := eq170 y (M.op y x)
       have i₂ := eq89566
       grind)
    | exact superpose eq89566 eq170
    | (have j0 := eq170 y (M.op y x)
       grind)
    | exact resolve eq170 eq89566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq89872 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op y (M.op y x)) = (k (M.op y x) y) := by
    first
    | (have i₁ := eq89843
       have i₂ := eq89560
       grind)
    | exact superpose eq89560 eq89843
    | exact resolve eq89843 eq89560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89843
  have eq89888 : (M.op y (M.op x y)) = (k (M.op x y) y) ∨ (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq89872
       have i₂ := eq89560
       grind)
    | exact superpose eq89560 eq89872
    | exact resolve eq89872 eq89560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89872
  have eq89898 : (M.op y (M.op x y)) = (k (M.op x y) y) := by
    first
    | (have j1 := eq78797 (M.op x y) y
       grind)
    | (have r₁ := eq89888
       have r₂ := eq78797 (M.op x y) y
       grind)
    | exact resolve eq89888 eq78797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78797 eq89888
  have eq94517 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq88129 y
       have i₂ := eq89488
       grind)
    | exact superpose eq89488 eq88129
    | exact resolve eq88129 eq89488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88129
  have eq94695 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq1610 y x
       have i₂ := eq94517
       grind)
    | exact superpose eq94517 eq1610
    | (have j0 := eq1610 y x
       grind)
    | exact resolve eq1610 eq94517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1610
  have eq95588 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (σ (k X1 X2)) = (σ (M.op X2 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq683 X2 X1
       have i₂ := eq89077 X0 X1
       grind)
    | (have i₁ := eq683 X0 X1
       have i₂ := eq89077 (M.op X1 X1) X1
       grind)
    | exact superpose eq89077 eq683
    | (have j0 := eq683 X2 X1
       have j1 := eq89077 X0 X1
       grind)
    | exact resolve eq683 eq89077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89077
  have eq97472 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = X0 ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq2070 x y X0
       grind)
    | exact superpose eq2070 eq14
    | (have j1 := eq2070 x y X0
       grind)
    | (have r₁ := eq14
       have r₂ := eq2070 (σ (M.op x y)) x (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq2070 (M.op (σ x) (σ y)) x (σ (M.op x y))
       grind)
    | exact resolve eq14 eq2070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070
  have eq97478 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq97472 X0
       have j1 := eq95588 (σ (k y X0)) x (M.op (σ X0) (σ y))
       grind)
    | (have r₁ := eq97472 X0
       have r₂ := eq95588 (σ (M.op x y)) x (σ (k y x))
       grind)
    | (have r₁ := eq97472 X0
       have r₂ := eq95588 (σ (k y x)) x (σ (M.op x y))
       grind)
    | (have r₁ := eq97472 X0
       have r₂ := eq95588 X0 y x
       grind)
    | exact resolve eq97472 eq95588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95588 eq97472
  have eq97575 : ∀ X0 : G, (M.op (σ (k y X0)) (σ y)) = (M.op (σ y) (σ (M.op y y))) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq87714 y (σ X0)
       have i₂ := eq97478 X0
       grind)
    | exact superpose eq97478 eq87714
    | (have j1 := eq97478 X0
       grind)
    | exact resolve eq87714 eq97478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87714 eq97478
  have eq97656 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ (k y X0)) (σ y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq97575 X0
       have i₂ := eq89488
       grind)
    | exact superpose eq89488 eq97575
    | (have j0 := eq97575 X0
       grind)
    | exact resolve eq97575 eq89488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97575
  have eq97710 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (k y X0)) (σ y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq97656 X0
       have i₂ := eq94517
       grind)
    | exact superpose eq94517 eq97656
    | (have j0 := eq97656 X0
       grind)
    | exact resolve eq97656 eq94517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94517 eq97656
  have eq100781 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq94695
       grind)
    | exact superpose eq94695 eq14
    | exact resolve eq14 eq94695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94695
  have eq100886 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq100781
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq100781
    | (have j1 := eq12 x y
       grind)
    | exact resolve eq100781 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100898 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (k x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq100781
       have i₂ := eq734 y x
       grind)
    | exact superpose eq734 eq100781
    | (have j1 := eq734 y x
       grind)
    | exact resolve eq100781 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734 eq100781
  have eq100904 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (k x y) := by grind
  clear eq100898
  have eq100910 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq100904
       have i₂ := eq89560
       grind)
    | exact superpose eq89560 eq100904
    | exact resolve eq100904 eq89560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100904
  have eq100911 : y = (k x y) := by grind
  clear eq100910
  have eq100930 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq100886
       have i₂ := eq89560
       grind)
    | exact superpose eq89560 eq100886
    | exact resolve eq100886 eq89560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100886
  have eq100931 : y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq100930
  have eq100941 : y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq100931
       have i₂ := eq89560
       grind)
    | exact superpose eq89560 eq100931
    | exact resolve eq100931 eq89560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100931
  have eq100992 : (τ y) = (τ (M.op y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14611 y x
       have i₂ := eq100911
       grind)
    | exact superpose eq100911 eq14611
    | (have j0 := eq14611 y x
       grind)
    | exact resolve eq14611 eq100911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14611
  have eq101008 : (τ y) = (τ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq100992
       have i₂ := eq89560
       grind)
    | exact superpose eq89560 eq100992
    | exact resolve eq100992 eq89560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100992
  have eq101124 : (M.op y y) = (M.op y (M.op y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8 y x
       have i₂ := eq100941
       grind)
    | exact superpose eq100941 eq8
    | exact resolve eq8 eq100941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100941
  have eq101168 : x = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq101124
       have i₂ := eq89488
       grind)
    | exact superpose eq89488 eq101124
    | exact resolve eq101124 eq89488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101124
  have eq101186 : x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq101168
       have i₂ := eq89560
       grind)
    | exact superpose eq89560 eq101168
    | exact resolve eq101168 eq89560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101168
  have eq101410 : x ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq89725
       have i₂ := eq101186
       grind)
    | exact superpose eq101186 eq89725
    | exact resolve eq89725 eq101186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89725
  have eq101467 : y = (M.op x x) ∨ x ≠ (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq101410
       have i₂ := eq100911
       grind)
    | exact superpose eq100911 eq101410
    | exact resolve eq101410 eq100911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101410
  have eq101468 : x ≠ (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq101467
  have eq101765 : (σ (M.op (τ y) (τ y))) = (k (M.op x y) (σ (M.op (τ y) (τ y)))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq21 (M.op x y)
       have i₂ := eq101008
       grind)
    | exact superpose eq101008 eq21
    | exact resolve eq21 eq101008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq101008
  have eq101805 : (σ (τ (M.op y y))) = (k (M.op x y) (σ (τ (M.op y y)))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq101765
       have i₂ := eq63391 y
       grind)
    | exact superpose eq63391 eq101765
    | exact resolve eq101765 eq63391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63391 eq101765
  have eq101815 : (M.op y y) = (k (M.op x y) (M.op y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq101805
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq101805
    | exact resolve eq101805 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101805
  have eq101818 : x = (k (M.op x y) x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq101815
       have i₂ := eq89488
       grind)
    | exact superpose eq89488 eq101815
    | exact resolve eq101815 eq89488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101815
  have eq103037 : x = (k x x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq101818
       have i₂ := eq101186
       grind)
    | exact superpose eq101186 eq101818
    | exact resolve eq101818 eq101186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101186 eq101818
  have eq103049 : x = (k x x) ∨ y = (M.op x x) := by grind
  clear eq103037
  have eq103054 : x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq103049
       have i₂ := eq61663 x
       grind)
    | exact superpose eq61663 eq103049
    | exact resolve eq103049 eq61663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103049
  have eq103055 : y = (M.op x x) := by
    first
    | (have r₁ := eq103054
       have r₂ := eq101468
       grind)
    | exact resolve eq103054 eq101468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101468 eq103054
  have eq112125 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (M.op X0 y)) (σ y)) ∨ x = X0 ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq97710 X0
       have i₂ := eq683 X0 y
       grind)
    | exact superpose eq683 eq97710
    | (have j0 := eq97710 X0
       have j1 := eq683 X0 y
       grind)
    | exact resolve eq97710 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683 eq97710
  have eq112221 : ∀ X0 : G, x = X0 ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op X0 y)) (σ y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq112125 X0
       have i₂ := eq89488
       grind)
    | exact superpose eq89488 eq112125
    | (have j0 := eq112125 X0
       grind)
    | exact resolve eq112125 eq89488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112125
  have eq112222 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (M.op X0 y)) (σ y)) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq112221 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112221
  have eq119914 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq60862 X0 X1
       have i₂ := eq78681 X0 X1
       grind)
    | exact superpose eq78681 eq60862
    | (have j1 := eq78681 X1 X0
       grind)
    | exact resolve eq60862 eq78681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60862 eq78681
  have eq120099 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq119914 X0 X1
       have i₂ := eq61663 X1
       grind)
    | exact superpose eq61663 eq119914
    | (have j0 := eq119914 X0 X1
       grind)
    | exact resolve eq119914 eq61663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119914
  have eq120145 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq120099 X0 X1
       have j1 := eq79155 X1 X0
       grind)
    | (have r₁ := eq120099 X1 X0
       have r₂ := eq79155 X0 X1
       grind)
    | (have r₁ := eq120099 X0 X0
       have r₂ := eq79155 X0 X0
       grind)
    | exact resolve eq120099 eq79155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79155 eq120099
  have eq127955 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op (M.op X0 y) y)) ∨ x = X0 ∨ (M.op y y) = (k y (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq112222 X0
       have i₂ := eq120145 (M.op X0 y) y
       grind)
    | exact superpose eq120145 eq112222
    | (have j0 := eq112222 X0
       have j1 := eq120145 (M.op X0 y) y
       grind)
    | exact resolve eq112222 eq120145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112222 eq120145
  have eq128140 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op y (M.op y y))) ∨ x = X0 ∨ (M.op y y) = (k y (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq127955 X0
       have i₂ := eq8 y X0
       grind)
    | exact superpose eq8 eq127955
    | (have j0 := eq127955 X0
       grind)
    | exact resolve eq127955 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127955
  have eq128192 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op y x)) ∨ x = X0 ∨ (M.op y y) = (k y (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq128140 X0
       have i₂ := eq89488
       grind)
    | exact superpose eq89488 eq128140
    | (have j0 := eq128140 X0
       grind)
    | exact resolve eq128140 eq89488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128140
  have eq128212 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = X0 ∨ (M.op y y) = (k y (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq128192 X0
       have i₂ := eq89560
       grind)
    | exact superpose eq89560 eq128192
    | (have j0 := eq128192 X0
       grind)
    | exact resolve eq128192 eq89560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128192
  have eq128220 : ∀ X0 : G, x = X0 ∨ (M.op y y) = (k y (M.op X0 y)) := by
    intro X0
    first
    | (have j0 := eq128212 X0
       grind)
    | (have r₁ := eq128212 X0
       have r₂ := eq14
       grind)
    | exact resolve eq128212 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128212
  have eq128222 : ∀ X0 : G, x = (k y (M.op X0 y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq128220 X0
       have i₂ := eq89488
       grind)
    | exact superpose eq89488 eq128220
    | (have j0 := eq128220 (k y (M.op X0 y))
       grind)
    | exact resolve eq128220 eq89488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128220
  have eq128239 : x = (k y (M.op y (M.op y y))) ∨ x = (M.op y (M.op y y)) := by
    first
    | (have i₁ := eq128222 (M.op y (M.op y y))
       have i₂ := eq19 y
       grind)
    | exact superpose eq19 eq128222
    | (have j0 := eq128222 (k y (M.op y (M.op y y)))
       grind)
    | exact resolve eq128222 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq128279 : x = (k y (M.op x y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq128222 (M.op y x)
       have i₂ := eq89566
       grind)
    | exact superpose eq89566 eq128222
    | (have j0 := eq128222 x
       grind)
    | exact resolve eq128222 eq89566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89566 eq128222
  have eq128487 : x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq128279
       have i₂ := eq89584
       grind)
    | exact superpose eq89584 eq128279
    | exact resolve eq128279 eq89584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89584 eq128279
  have eq128515 : x = (M.op y (M.op y y)) ∨ x = (M.op y (M.op y y)) := by
    first
    | (have i₁ := eq128239
       have i₂ := eq104 y
       grind)
    | exact superpose eq104 eq128239
    | exact resolve eq128239 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq128239
  have eq128516 : x = (M.op y (M.op y y)) := by grind
  clear eq128515
  have eq128611 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq128487
       have i₂ := eq89560
       grind)
    | exact superpose eq89560 eq128487
    | exact resolve eq128487 eq89560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89560 eq128487
  have eq128612 : x = (M.op x y) := by grind
  clear eq128611
  have eq128641 : x = (M.op y x) := by
    first
    | (have i₁ := eq128516
       have i₂ := eq89488
       grind)
    | exact superpose eq89488 eq128516
    | exact resolve eq128516 eq89488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89488 eq128516
  have eq128779 : (M.op y x) = (k x y) := by
    first
    | (have i₁ := eq89898
       have i₂ := eq128612
       grind)
    | exact superpose eq128612 eq89898
    | exact resolve eq89898 eq128612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89898 eq128612
  have eq128963 : y = (M.op y x) := by
    first
    | (have i₁ := eq128779
       have i₂ := eq100911
       grind)
    | exact superpose eq100911 eq128779
    | exact resolve eq128779 eq100911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100911 eq128779
  have eq129005 : x = y := by
    first
    | (have i₁ := eq128963
       have i₂ := eq128641
       grind)
    | exact superpose eq128641 eq128963
    | exact resolve eq128963 eq128641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128641 eq128963
  have eq129053 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq129005
       grind)
    | exact superpose eq129005 eq14
    | exact resolve eq14 eq129005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129005
  have eq129287 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq129053
       have i₂ := eq103055
       grind)
    | exact superpose eq103055 eq129053
    | exact resolve eq129053 eq103055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129053
  have eq129312 : (σ y) ≠ (σ (k x x)) := by
    first
    | (have i₁ := eq129287
       have i₂ := eq60036 x
       grind)
    | exact superpose eq60036 eq129287
    | exact resolve eq129287 eq60036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60036 eq129287
  have eq129321 : (σ y) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq129312
       have i₂ := eq61663 x
       grind)
    | exact superpose eq61663 eq129312
    | exact resolve eq129312 eq61663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61663 eq129312
  have eq129325 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq129321
       have i₂ := eq103055
       grind)
    | exact superpose eq103055 eq129321
    | exact resolve eq129321 eq103055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103055 eq129321
  have eq129326 : False := by grind
  exact eq129326

/-- `Equation4386`: `x ◇ (x ◇ x) = (y ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation4386 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4386 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4386.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X0) X1) := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq18 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X2 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq8 X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X0 (M.op X0 X0)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X1 X0)
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X1) X2) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq31 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X2 X1)) = (M.op X2 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op X2 X1)
       have i₂ := eq18 X2 X1 X0
       grind)
    | (have i₁ := eq8 X2 (M.op X2 X1)
       have i₂ := eq18 X0 X1 X2
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq29
    | exact resolve eq29 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq29 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq39
  have eq123 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq108 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq108
    | exact resolve eq108 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq135 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq19 X0 X1
       have i₂ := eq12 X0 (M.op X1 X0)
       grind)
    | exact superpose eq12 eq19
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq19 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op (M.op X0 X1) X0) ∨ (M.op X1 X1) = (k (M.op X1 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq77 (M.op X1 X1) X1
       have i₂ := eq8 X1 X0
       grind)
    | exact superpose eq8 eq77
    | (have j0 := eq77 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq77 (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) X0)
       have r₂ := eq8 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq77 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq183 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = X2 ∨ (M.op X2 X1) = (k X1 X2) ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq28 X1 X1 X0
       grind)
    | exact superpose eq28 eq12
    | (have j0 := eq12 X1 (k X1 X1)
       have j1 := eq28 X2 X1 X2
       grind)
    | exact resolve eq12 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X2) = (M.op X1 (M.op (M.op X0 X1) X0)) ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq28 X1 X1 X0
       grind)
    | exact superpose eq28 eq8
    | (have j1 := eq28 (M.op (M.op X0 X1) X0) X1 X2
       grind)
    | exact resolve eq8 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (M.op X2 (σ X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq28 (σ X0) (σ X1) X2
       grind)
    | exact superpose eq28 eq13
    | (have j1 := eq28 (σ X0) (σ X1) X2
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq298 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq31 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq31
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq31 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq325 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq9
    | (have j1 := eq31 X1 X0
       grind)
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq335 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq123 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq123
    | (have j1 := eq31 X0 X1
       grind)
    | exact resolve eq123 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq352 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq335 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq335
    | (have j0 := eq335 X0 X1
       grind)
    | exact resolve eq335 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq1125 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq34
    | exact resolve eq34 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq1223 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1125 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1125
    | (have j0 := eq1125 X0 X1
       grind)
    | exact resolve eq1125 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125
  have eq1475 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq2335 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq71 X0 X0
       grind)
    | exact superpose eq71 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq71 X0 X0
       grind)
    | exact resolve eq12 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq2775 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (τ (σ X0)) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq325 X1 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq325
    | (have j0 := eq325 X1 X0
       have j1 := eq31 X0 X1
       grind)
    | exact resolve eq325 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq325
  have eq2826 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2775 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2775
    | (have j0 := eq2775 X0 X1
       grind)
    | exact resolve eq2775 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2775
  have eq7029 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X1 X0) X1)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq135 X0 X0
       have i₂ := eq184 X1 X0 X0
       grind)
    | exact superpose eq184 eq135
    | (have j0 := eq135 X0 X0
       have j1 := eq184 X0 X0 x
       grind)
    | exact resolve eq135 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq7123 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X1 X0) X1)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq7029 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7029
  have eq11751 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq352 x y
       grind)
    | exact superpose eq352 eq14
    | (have j1 := eq352 x y
       grind)
    | exact resolve eq14 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11859 : y = (k y x) := by
    first
    | (have j1 := eq1475 x y
       grind)
    | (have r₁ := eq11751
       have r₂ := eq1475 x y
       grind)
    | exact resolve eq11751 eq1475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11751
  have eq12166 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X1 X0) X1) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq183 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq12167 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12166 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12166
  have eq12265 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1223 x y
       have i₂ := eq11859
       grind)
    | exact superpose eq11859 eq1223
    | (have j0 := eq1223 x y
       grind)
    | exact resolve eq1223 eq11859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13658 : ∀ X0 X1 : G, (σ (k X0 X0)) ≠ (M.op (M.op X1 (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq211 X0 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq14586 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op X2 X0) X2)) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq184 X2 X0 x
       have i₂ := eq12167 X0 x
       grind)
    | exact superpose eq12167 eq184
    | (have j0 := eq184 X0 X0 X2
       have j1 := eq12167 X0 x
       grind)
    | exact resolve eq184 eq12167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq14707 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op X2 X0) X2)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X2
    first
    | (have j0 := eq14586 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14586
  have eq58255 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq149 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq149 X0 X1
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq149
    | (have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq149 X0 X0
       have r₂ := eq12 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq149 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq70258 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y y)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq2826 x y
       grind)
    | exact superpose eq2826 eq14
    | (have j1 := eq2826 x y
       grind)
    | (have r₁ := eq14
       have r₂ := eq2826 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq2826 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq14 eq2826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2826
  have eq70265 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (k y y)) ∨ x = y := by
    first
    | (have i₁ := eq70258
       have i₂ := eq11859
       grind)
    | exact superpose eq11859 eq70258
    | exact resolve eq70258 eq11859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70258
  have eq70532 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k y y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq70265
       have i₂ := eq12265
       grind)
    | exact superpose eq12265 eq70265
    | (have r₁ := eq70265
       have r₂ := eq12265
       grind)
    | exact resolve eq70265 eq12265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70265
  have eq70533 : (σ x) = (σ (k y y)) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq70532
  have eq70588 : (k y y) = (τ (σ x)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq70533
       grind)
    | exact superpose eq70533 eq9
    | exact resolve eq9 eq70533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70533
  have eq70599 : x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq70588
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq70588
    | exact resolve eq70588 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70588
  have eq70700 : x = (M.op y y) ∨ x = y ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq29 y y
       have i₂ := eq70599
       grind)
    | exact superpose eq70599 eq29
    | exact resolve eq29 eq70599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq70599
  have eq70730 : x = (M.op y y) ∨ x = y := by grind
  clear eq70700
  have eq70967 : x = (M.op y (M.op x y)) ∨ x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq7123 y y
       have i₂ := eq70730
       grind)
    | exact superpose eq70730 eq7123
    | exact resolve eq7123 eq70730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7123
  have eq70973 : y = (M.op y (M.op x y)) ∨ x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq14707 y y
       have i₂ := eq70730
       grind)
    | exact superpose eq70730 eq14707
    | exact resolve eq14707 eq70730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14707
  have eq75777 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) ≠ (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13658 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13658
    | exact resolve eq13658 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13658
  have eq75783 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) ≠ (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq75777 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq75777
    | (have j0 := eq75777 X0 X1
       grind)
    | exact resolve eq75777 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75777
  have eq75784 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) ≠ (k X0 X0) ∨ (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq75783 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq75783
    | (have j0 := eq75783 X0 X1
       grind)
    | exact resolve eq75783 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75783
  have eq75785 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op (M.op X1 X0) X1) ≠ (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq75784 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq75784
    | (have j0 := eq75784 X0 X1
       grind)
    | exact resolve eq75784 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75784
  have eq75786 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) ≠ (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq75785 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq75785
    | (have j0 := eq75785 X0 X1
       grind)
    | exact resolve eq75785 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75785
  have eq76154 : x = y ∨ x = (k y y) ∨ x = y ∨ x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq70967
       have i₂ := eq70973
       grind)
    | exact superpose eq70973 eq70967
    | exact resolve eq70967 eq70973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70967 eq70973
  have eq76171 : x = (k y y) ∨ x = y := by grind
  clear eq76154
  have eq77724 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2335 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2335
  have eq77725 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq77724 X0 X1
       have j1 := eq298 X1 X0
       grind)
    | (have r₁ := eq77724 (k X1 X1) X0
       have r₂ := eq298 X0 X1
       grind)
    | (have r₁ := eq77724 X0 (σ (k X1 X1))
       have r₂ := eq298 (σ X0) X1
       grind)
    | (have r₁ := eq77724 X1 X0
       have r₂ := eq298 X0 X1
       grind)
    | exact resolve eq77724 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298 eq77724
  have eq77763 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq77725 (τ X1) X0
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq77725 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq77725 eq16
    | (have j1 := eq77725 (τ X1) X0
       grind)
    | exact resolve eq16 eq77725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq77764 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq77725 X1 X0
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq77725 X0 (σ X0)
       grind)
    | exact superpose eq77725 eq9
    | (have j1 := eq77725 X1 X0
       grind)
    | exact resolve eq9 eq77725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77725
  have eq77788 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq77763 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq77763
    | (have j0 := eq77763 X0 X1
       grind)
    | exact resolve eq77763 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77763
  have eq77794 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq77788 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq77788
    | (have j0 := eq77788 X0 X1
       grind)
    | exact resolve eq77788 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77788
  have eq78535 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (τ (σ X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq77764 (σ X0) X1
       grind)
    | exact superpose eq77764 eq13
    | (have j1 := eq77764 (σ X0) X1
       grind)
    | exact resolve eq13 eq77764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77764
  have eq78543 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq78535 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq78535
    | (have j0 := eq78535 X0 X1
       grind)
    | exact resolve eq78535 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78535
  have eq79380 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq78543 x y
       grind)
    | exact superpose eq78543 eq14
    | (have j1 := eq78543 x y
       grind)
    | exact resolve eq14 eq78543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79400 : (σ (M.op x y)) ≠ (σ y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq79380
       have i₂ := eq11859
       grind)
    | exact superpose eq11859 eq79380
    | exact resolve eq79380 eq11859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11859 eq79380
  have eq79428 : (σ y) ≠ (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq79400
       have i₂ := eq12265
       grind)
    | exact superpose eq12265 eq79400
    | (have r₁ := eq79400
       have r₂ := eq12265
       grind)
    | exact resolve eq79400 eq12265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12265 eq79400
  have eq79429 : x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq79428
  have eq79534 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq79429
       grind)
    | exact superpose eq79429 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq79429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79429
  have eq79572 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq79534
  have eq80107 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq79572
  have eq80130 : x = (M.op y y) := by
    first
    | (have r₁ := eq80107
       have r₂ := eq70730
       grind)
    | exact resolve eq80107 eq70730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70730 eq80107
  have eq80301 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq8 y y
       have i₂ := eq80130
       grind)
    | exact superpose eq80130 eq8
    | exact resolve eq8 eq80130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80311 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op x y) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq61 y y X0
       have i₂ := eq80130
       grind)
    | exact superpose eq80130 eq61
    | exact resolve eq61 eq80130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq80469 : x ≠ y ∨ y = (k y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq58255 y y
       have i₂ := eq80130
       grind)
    | exact superpose eq80130 eq58255
    | (have j0 := eq58255 y y
       grind)
    | exact resolve eq58255 eq80130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58255
  have eq80477 : y = (k y y) ∨ x = (k y y) := by
    first
    | (have r₁ := eq80469
       have r₂ := eq76171
       grind)
    | exact resolve eq80469 eq76171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80469
  have eq82213 : x ≠ y ∨ x = (k y y) := by grind
  clear eq80477
  have eq82243 : x = (k y y) := by
    first
    | (have r₁ := eq82213
       have r₂ := eq76171
       grind)
    | exact resolve eq82213 eq76171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76171 eq82213
  have eq82388 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq77794 X0 y
       have i₂ := eq82243
       grind)
    | exact superpose eq82243 eq77794
    | (have j0 := eq77794 X0 y
       grind)
    | exact resolve eq77794 eq82243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82243
  have eq82589 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op (τ X0) y)) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq17 X0 y
       have i₂ := eq82388 (τ X0)
       grind)
    | exact superpose eq82388 eq17
    | (have j1 := eq82388 (τ X0)
       grind)
    | exact resolve eq17 eq82388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq82388
  have eq97164 : ∀ X0 : G, (σ (M.op X0 y)) = (k (σ y) (σ X0)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq82589 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq82589
    | exact resolve eq82589 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82589
  have eq97185 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq97164 X0
       have i₂ := eq13 y X0
       grind)
    | exact superpose eq13 eq97164
    | (have j0 := eq97164 X0
       grind)
    | exact resolve eq97164 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97164
  have eq104969 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq75786 X0 x
       have i₂ := eq12167 X0 x
       grind)
    | exact superpose eq12167 eq75786
    | (have j0 := eq75786 X0 x
       have j1 := eq12167 X0 x
       grind)
    | exact resolve eq75786 eq12167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12167 eq75786
  have eq105001 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq104969 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104969
  have eq105019 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq105001 X0
       have j1 := eq77794 X0 X0
       grind)
    | (have r₁ := eq105001 X0
       have r₂ := eq77794 X0 X0
       grind)
    | (have r₁ := eq105001 (k x x)
       have r₂ := eq77794 (k (k x x) (k x x)) x
       grind)
    | exact resolve eq105001 eq77794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77794 eq105001
  have eq105252 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq105019 (σ X0)
       grind)
    | exact superpose eq105019 eq13
    | exact resolve eq13 eq105019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105332 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq105252 X0
       have i₂ := eq105019 X0
       grind)
    | exact superpose eq105019 eq105252
    | exact resolve eq105252 eq105019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105252
  have eq105850 : ∀ X0 X1 : G, (M.op (M.op X1 (σ X0)) X1) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X0) X1
       have i₂ := eq105332 X0
       grind)
    | exact superpose eq105332 eq8
    | exact resolve eq8 eq105332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105898 : ∀ X0 X1 : G, (M.op (M.op X1 (σ X0)) X1) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (σ X0) (σ X0)
       have i₂ := eq105332 X0
       grind)
    | exact superpose eq105332 eq18
    | exact resolve eq18 eq105332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq108231 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq105850 y X0
       have i₂ := eq80130
       grind)
    | exact superpose eq80130 eq105850
    | exact resolve eq105850 eq80130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105850
  have eq108520 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ (k y X0)) (σ X0)) ∨ (k y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq108231 (σ X0)
       have i₂ := eq78543 X0 y
       grind)
    | exact superpose eq78543 eq108231
    | (have j1 := eq78543 X0 y
       grind)
    | exact resolve eq108231 eq78543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108910 : ∀ X0 : G, (M.op y y) = X0 ∨ (M.op (σ y) (σ x)) = (M.op (σ (k y X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq108520 X0
       have i₂ := eq105019 y
       grind)
    | exact superpose eq105019 eq108520
    | (have j0 := eq108520 X0
       grind)
    | exact resolve eq108520 eq105019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108520
  have eq109023 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ (k y X0)) (σ X0)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq108910 X0
       have i₂ := eq80130
       grind)
    | exact superpose eq80130 eq108910
    | (have j0 := eq108910 X0
       grind)
    | exact resolve eq108910 eq80130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108910
  have eq109176 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq105898 y X0
       have i₂ := eq80130
       grind)
    | exact superpose eq80130 eq105898
    | exact resolve eq105898 eq80130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80130 eq105898
  have eq109626 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq108231 x
       have i₂ := eq109176 x
       grind)
    | exact superpose eq109176 eq108231
    | exact resolve eq108231 eq109176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108231 eq109176
  have eq110255 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq352 y x
       have i₂ := eq109626
       grind)
    | exact superpose eq109626 eq352
    | (have j0 := eq352 y x
       grind)
    | exact resolve eq352 eq109626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq110260 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq78543 y x
       have i₂ := eq109626
       grind)
    | exact superpose eq109626 eq78543
    | (have j0 := eq78543 y x
       grind)
    | exact resolve eq78543 eq109626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78543
  have eq110320 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq110260
       have i₂ := eq105019 x
       grind)
    | exact superpose eq105019 eq110260
    | exact resolve eq110260 eq105019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105019 eq110260
  have eq113771 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq110255
       grind)
    | exact superpose eq110255 eq14
    | exact resolve eq14 eq110255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110255
  have eq113824 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq113771
       have i₂ := eq1475 y x
       grind)
    | exact superpose eq1475 eq113771
    | (have j1 := eq1475 y x
       grind)
    | exact resolve eq113771 eq1475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475 eq113771
  have eq113826 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = (k x y) := by grind
  clear eq113824
  have eq113827 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq113826
       have i₂ := eq80301
       grind)
    | exact superpose eq80301 eq113826
    | exact resolve eq113826 eq80301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113826
  have eq113828 : x = (k x y) := by grind
  clear eq113827
  have eq113872 : (σ x) = (σ (M.op y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1223 y x
       have i₂ := eq113828
       grind)
    | exact superpose eq113828 eq1223
    | (have j0 := eq1223 y x
       grind)
    | exact resolve eq1223 eq113828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1223
  have eq113906 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq113872
       have i₂ := eq80301
       grind)
    | exact superpose eq80301 eq113872
    | exact resolve eq113872 eq80301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80301 eq113872
  have eq116340 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq110320
       grind)
    | exact superpose eq110320 eq14
    | exact resolve eq14 eq110320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110320
  have eq116369 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq116340
       have i₂ := eq113828
       grind)
    | exact superpose eq113828 eq116340
    | exact resolve eq116340 eq113828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113828 eq116340
  have eq116377 : y = (M.op x x) := by
    first
    | (have r₁ := eq116369
       have r₂ := eq113906
       grind)
    | exact resolve eq116369 eq113906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113906 eq116369
  have eq116419 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op x y) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq19 x X0
       have i₂ := eq116377
       grind)
    | exact superpose eq116377 eq19
    | exact resolve eq19 eq116377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116543 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq19 x x
       have i₂ := eq116377
       grind)
    | exact superpose eq116377 eq19
    | exact resolve eq19 eq116377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq118947 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op (M.op x y) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq80311 X0
       have i₂ := eq116419 X0
       grind)
    | exact superpose eq116419 eq80311
    | exact resolve eq80311 eq116419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116419
  have eq131575 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ (M.op X0 y)) (σ X0)) ∨ x = X0 ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq109023 X0
       have i₂ := eq97185 X0
       grind)
    | exact superpose eq97185 eq109023
    | (have j0 := eq109023 X0
       have j1 := eq97185 X0
       grind)
    | exact resolve eq109023 eq97185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97185 eq109023
  have eq131582 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ (M.op X0 y)) (σ X0)) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq131575 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131575
  have eq131591 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (M.op X0 y)) (σ X0)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq131582 X0
       have i₂ := eq109626
       grind)
    | exact superpose eq109626 eq131582
    | (have j0 := eq131582 X0
       grind)
    | exact resolve eq131582 eq109626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109626 eq131582
  have eq136182 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq131591 (M.op x y)
       have i₂ := eq116543
       grind)
    | exact superpose eq116543 eq131591
    | (have j0 := eq131591 (M.op x y)
       grind)
    | exact resolve eq131591 eq116543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116543 eq131591
  have eq136198 : (M.op (σ x) (σ y)) = (σ (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq136182
       have i₂ := eq105332 (M.op x y)
       grind)
    | exact superpose eq105332 eq136182
    | exact resolve eq136182 eq105332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136182
  have eq136199 : (M.op (σ x) (σ y)) = (σ (M.op x (M.op x x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq136198
       have i₂ := eq80311 x
       grind)
    | exact superpose eq80311 eq136198
    | exact resolve eq136198 eq80311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80311 eq136198
  have eq136200 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq136199
       have i₂ := eq116377
       grind)
    | exact superpose eq116377 eq136199
    | exact resolve eq136199 eq116377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136199
  have eq136201 : x = (M.op x y) := by
    first
    | (have r₁ := eq136200
       have r₂ := eq14
       grind)
    | exact resolve eq136200 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136200
  have eq136352 : (M.op x x) = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq118947 x
       have i₂ := eq136201
       grind)
    | exact superpose eq136201 eq118947
    | exact resolve eq118947 eq136201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118947
  have eq136686 : y = (M.op x y) := by
    first
    | (have i₁ := eq136352
       have i₂ := eq116377
       grind)
    | exact superpose eq116377 eq136352
    | exact resolve eq136352 eq116377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116377 eq136352
  have eq136848 : x = y := by
    first
    | (have i₁ := eq136686
       have i₂ := eq136201
       grind)
    | exact superpose eq136201 eq136686
    | exact resolve eq136686 eq136201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136201 eq136686
  have eq137233 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq136848
       grind)
    | exact superpose eq136848 eq14
    | exact resolve eq14 eq136848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136848
  have eq137712 : False := by grind
  exact eq137712

/-- `Equation4386`: `x ◇ (x ◇ x) = (y ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_x_y_pxy_Equation4386 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4386 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4386.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X0) X1) := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq18 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X2 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq8 X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X0 (M.op X0 X0)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X1 X0)
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq26 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X1) X2) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 (M.op X0 X0) X1
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq29 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq30 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 (τ X0) X1
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X2 X1)) = (M.op X2 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op X2 X1)
       have i₂ := eq18 X2 X1 X0
       grind)
    | (have i₁ := eq8 X2 (M.op X2 X1)
       have i₂ := eq18 X0 X1 X2
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    grind
  clear eq23
  have eq72 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq65
    | exact resolve eq65 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq27 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq27
    | exact resolve eq27 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq19 X0 X1
       have i₂ := eq12 (M.op X1 X0) X1
       grind)
    | exact superpose eq12 eq19
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq19 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op (M.op X0 X1) X0) ∨ (M.op X1 X1) = (k X1 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq79 X1 (M.op X1 X1)
       have i₂ := eq8 X1 X0
       grind)
    | exact superpose eq8 eq79
    | (have j0 := eq79 X1 (M.op X1 X1)
       grind)
    | (have r₁ := eq79 (M.op (M.op X0 (M.op X0 X0)) X0) (M.op X0 (M.op X0 X0))
       have r₂ := eq8 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq79 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq185 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = X2 ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq26 X1 X1 X0
       grind)
    | exact superpose eq26 eq12
    | (have j0 := eq12 (k X1 X1) X1
       have j1 := eq26 X2 X1 X2
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X2) = (M.op X1 (M.op (M.op X0 X1) X0)) ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq26 X1 X1 X0
       grind)
    | exact superpose eq26 eq8
    | (have j1 := eq26 (M.op (M.op X0 X1) X0) X1 X2
       grind)
    | exact resolve eq8 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (M.op X2 (σ X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq26 (σ X0) (σ X1) X2
       grind)
    | exact superpose eq26 eq13
    | (have j1 := eq26 (σ X0) (σ X1) X2
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq301 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X0
       have i₂ := eq12 X0 (σ X0)
       grind)
    | (have i₁ := eq29 X0 X1
       have i₂ := eq12 (M.op (σ X0) (σ X1)) X1
       grind)
    | exact superpose eq12 eq29
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq29 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq328 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq29 X1 X0
       grind)
    | exact superpose eq29 eq9
    | (have j1 := eq29 X1 X0
       grind)
    | exact resolve eq9 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X1
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq72
    | (have j1 := eq29 X0 X1
       grind)
    | exact resolve eq72 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq355 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq338 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq338
    | (have j0 := eq338 X0 X1
       grind)
    | exact resolve eq338 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq1130 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq30
    | exact resolve eq30 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq1228 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1130 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1130
    | (have j0 := eq1130 X0 X1
       grind)
    | exact resolve eq1130 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130
  have eq1480 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq2342 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq73 X0 X0
       grind)
    | exact superpose eq73 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq73 X0 X0
       grind)
    | exact resolve eq12 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq2834 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (τ (σ X0)) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq328 X1 X1
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq328
    | (have j0 := eq328 X1 X0
       have j1 := eq29 X0 X1
       grind)
    | exact resolve eq328 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq328
  have eq2885 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X1 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2834 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2834
    | (have j0 := eq2834 X0 X1
       grind)
    | exact resolve eq2834 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2834
  have eq7202 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X1 X0) X1)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq137 X0 X0
       have i₂ := eq186 X1 X0 X0
       grind)
    | exact superpose eq186 eq137
    | (have j0 := eq137 X0 X0
       have j1 := eq186 X0 X0 x
       grind)
    | exact resolve eq137 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq7296 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X1 X0) X1)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq7202 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7202
  have eq10201 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq355 x y
       grind)
    | exact superpose eq355 eq14
    | (have j1 := eq355 x y
       grind)
    | exact resolve eq14 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10300 : y = (k x y) := by
    first
    | (have j1 := eq1480 x y
       grind)
    | (have r₁ := eq10201
       have r₂ := eq1480 x y
       grind)
    | exact resolve eq10201 eq1480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10201
  have eq11014 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1228 x y
       have i₂ := eq10300
       grind)
    | exact superpose eq10300 eq1228
    | (have j0 := eq1228 x y
       grind)
    | exact resolve eq1228 eq10300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12104 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X1 X0) X1) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq185 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq12105 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12104 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12104
  have eq13543 : ∀ X0 X1 : G, (σ (k X0 X0)) ≠ (M.op (M.op X1 (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq212 X0 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq13741 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op X2 X0) X2)) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq186 X2 X0 x
       have i₂ := eq12105 X0 x
       grind)
    | exact superpose eq12105 eq186
    | (have j0 := eq186 X0 X0 X2
       have j1 := eq12105 X0 x
       grind)
    | exact resolve eq186 eq12105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq13862 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op X2 X0) X2)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X2
    first
    | (have j0 := eq13741 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13741
  have eq72612 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq151 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq151 X0 X1
       have i₂ := eq12 (M.op X0 X1) X1
       grind)
    | exact superpose eq12 eq151
    | (have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq151 X0 X1
       have r₂ := eq12 (M.op (M.op X0 X1) X0) X1
       grind)
    | exact resolve eq151 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq131859 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k y y)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq2885 x y
       grind)
    | exact superpose eq2885 eq14
    | (have j1 := eq2885 x y
       grind)
    | (have r₁ := eq14
       have r₂ := eq2885 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq2885 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq14 eq2885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2885
  have eq131872 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (k y y)) ∨ x = y := by
    first
    | (have i₁ := eq131859
       have i₂ := eq10300
       grind)
    | exact superpose eq10300 eq131859
    | exact resolve eq131859 eq10300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131859
  have eq132684 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k y y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq131872
       have i₂ := eq11014
       grind)
    | exact superpose eq11014 eq131872
    | (have r₁ := eq131872
       have r₂ := eq11014
       grind)
    | exact resolve eq131872 eq11014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131872
  have eq132685 : (σ x) = (σ (k y y)) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq132684
  have eq132818 : (k y y) = (τ (σ x)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq132685
       grind)
    | exact superpose eq132685 eq9
    | exact resolve eq9 eq132685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132685
  have eq132833 : x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq132818
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq132818
    | exact resolve eq132818 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132818
  have eq133062 : x = (M.op y y) ∨ x = y ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq27 y y
       have i₂ := eq132833
       grind)
    | exact superpose eq132833 eq27
    | exact resolve eq27 eq132833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq132833
  have eq133092 : x = (M.op y y) ∨ x = y := by grind
  clear eq133062
  have eq133343 : x = (M.op y (M.op x y)) ∨ x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq7296 y y
       have i₂ := eq133092
       grind)
    | exact superpose eq133092 eq7296
    | exact resolve eq7296 eq133092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7296
  have eq133350 : y = (M.op y (M.op x y)) ∨ x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq13862 y y
       have i₂ := eq133092
       grind)
    | exact superpose eq133092 eq13862
    | exact resolve eq13862 eq133092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13862
  have eq138608 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) ≠ (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13543 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13543
    | exact resolve eq13543 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13543
  have eq138616 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) ≠ (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq138608 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq138608
    | (have j0 := eq138608 X0 X1
       grind)
    | exact resolve eq138608 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138608
  have eq138617 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) ≠ (k X0 X0) ∨ (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq138616 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq138616
    | (have j0 := eq138616 X0 X1
       grind)
    | exact resolve eq138616 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138616
  have eq138618 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op (M.op X1 X0) X1) ≠ (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq138617 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq138617
    | (have j0 := eq138617 X0 X1
       grind)
    | exact resolve eq138617 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq138617
  have eq138619 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) ≠ (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq138618 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq138618
    | (have j0 := eq138618 X0 X1
       grind)
    | exact resolve eq138618 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138618
  have eq139362 : x = y ∨ x = (k y y) ∨ x = y ∨ x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq133343
       have i₂ := eq133350
       grind)
    | exact superpose eq133350 eq133343
    | exact resolve eq133343 eq133350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133343 eq133350
  have eq139381 : x = (k y y) ∨ x = y := by grind
  clear eq139362
  have eq141046 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2342 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2342
  have eq141047 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq141046 X0 X1
       have j1 := eq301 X1 X0
       grind)
    | (have r₁ := eq141046 (k X1 X1) X0
       have r₂ := eq301 X0 X1
       grind)
    | (have r₁ := eq141046 X0 (σ (k X1 X1))
       have r₂ := eq301 (σ X0) X1
       grind)
    | (have r₁ := eq141046 X1 X0
       have r₂ := eq301 X0 X1
       grind)
    | exact resolve eq141046 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301 eq141046
  have eq141205 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k X0 (σ (τ X1))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq141047 (τ X1) X0
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq141047 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq141047 eq16
    | (have j1 := eq141047 (τ X1) X0
       grind)
    | exact resolve eq16 eq141047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141206 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq141047 X1 X0
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq141047 X0 (σ X0)
       grind)
    | exact superpose eq141047 eq9
    | (have j1 := eq141047 X1 X0
       grind)
    | exact resolve eq9 eq141047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141047
  have eq141247 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k X0 (σ (τ X1))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq141205 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq141205
    | (have j0 := eq141205 X0 X1
       grind)
    | exact resolve eq141205 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141205
  have eq141253 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq141247 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq141247
    | (have j0 := eq141247 X0 X1
       grind)
    | exact resolve eq141247 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141247
  have eq142165 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq141206 (σ X0) X1
       grind)
    | exact superpose eq141206 eq13
    | (have j1 := eq141206 (σ X0) X1
       grind)
    | exact resolve eq13 eq141206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141206
  have eq142181 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq142165 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq142165
    | (have j0 := eq142165 X0 X1
       grind)
    | exact resolve eq142165 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142165
  have eq143323 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq142181 x y
       grind)
    | exact superpose eq142181 eq14
    | (have j1 := eq142181 x y
       grind)
    | exact resolve eq14 eq142181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143366 : (σ (M.op x y)) ≠ (σ y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq143323
       have i₂ := eq10300
       grind)
    | exact superpose eq10300 eq143323
    | exact resolve eq143323 eq10300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10300 eq143323
  have eq143411 : (σ y) ≠ (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq143366
       have i₂ := eq11014
       grind)
    | exact superpose eq11014 eq143366
    | (have r₁ := eq143366
       have r₂ := eq11014
       grind)
    | exact resolve eq143366 eq11014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11014 eq143366
  have eq143413 : x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq143411
  have eq143534 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq143413
       grind)
    | exact superpose eq143413 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq143413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143413
  have eq143572 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq143534
  have eq144216 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq143572
  have eq144239 : x = (M.op y y) := by
    first
    | (have r₁ := eq144216
       have r₂ := eq133092
       grind)
    | exact resolve eq144216 eq133092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133092 eq144216
  have eq144424 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq8 y y
       have i₂ := eq144239
       grind)
    | exact superpose eq144239 eq8
    | exact resolve eq8 eq144239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144434 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op x y) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq61 y y X0
       have i₂ := eq144239
       grind)
    | exact superpose eq144239 eq61
    | exact resolve eq61 eq144239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq144595 : x ≠ y ∨ y = (k y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq72612 y y
       have i₂ := eq144239
       grind)
    | exact superpose eq144239 eq72612
    | (have j0 := eq72612 y y
       grind)
    | exact resolve eq72612 eq144239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72612
  have eq144603 : y = (k y y) ∨ x = (k y y) := by
    first
    | (have r₁ := eq144595
       have r₂ := eq139381
       grind)
    | exact resolve eq144595 eq139381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144595
  have eq146413 : x ≠ y ∨ x = (k y y) := by grind
  clear eq144603
  have eq146445 : x = (k y y) := by
    first
    | (have r₁ := eq146413
       have r₂ := eq139381
       grind)
    | exact resolve eq146413 eq139381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139381 eq146413
  have eq146606 : ∀ X0 : G, (M.op X0 y) = (k X0 y) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq141253 X0 y
       have i₂ := eq146445
       grind)
    | exact superpose eq146445 eq141253
    | (have j0 := eq141253 X0 y
       grind)
    | exact resolve eq141253 eq146445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146800 : ∀ X0 : G, (k X0 (σ y)) = (σ (M.op (τ X0) y)) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq16 X0 y
       have i₂ := eq146606 (τ X0)
       grind)
    | exact superpose eq146606 eq16
    | (have j1 := eq146606 (τ X0)
       grind)
    | exact resolve eq16 eq146606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq146606
  have eq171544 : ∀ X0 : G, (σ (M.op X0 y)) = (k (σ X0) (σ y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq146800 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq146800
    | exact resolve eq146800 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146800
  have eq171570 : ∀ X0 : G, (σ (k X0 y)) = (σ (M.op X0 y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq171544 X0
       have i₂ := eq13 X0 y
       grind)
    | exact superpose eq13 eq171544
    | (have j0 := eq171544 X0
       grind)
    | exact resolve eq171544 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171544
  have eq191119 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq138619 X0 x
       have i₂ := eq12105 X0 x
       grind)
    | exact superpose eq12105 eq138619
    | (have j0 := eq138619 X0 x
       have j1 := eq12105 X0 x
       grind)
    | exact resolve eq138619 eq12105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12105 eq138619
  have eq191157 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq191119 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191119
  have eq191175 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq191157 X0
       have j1 := eq141253 X0 X0
       grind)
    | (have r₁ := eq191157 X0
       have r₂ := eq141253 X0 X0
       grind)
    | (have r₁ := eq191157 (k x x)
       have r₂ := eq141253 (k (k x x) (k x x)) x
       grind)
    | exact resolve eq191157 eq141253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141253 eq191157
  have eq191545 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq191175 (σ X0)
       grind)
    | exact superpose eq191175 eq13
    | exact resolve eq13 eq191175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191639 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq191545 X0
       have i₂ := eq191175 X0
       grind)
    | exact superpose eq191175 eq191545
    | exact resolve eq191545 eq191175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191545
  have eq192764 : ∀ X0 X1 : G, (M.op (M.op X1 (σ X0)) X1) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X0) X1
       have i₂ := eq191639 X0
       grind)
    | exact superpose eq191639 eq8
    | exact resolve eq8 eq191639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192862 : ∀ X0 X1 : G, (M.op (M.op X1 (σ X0)) X1) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (σ X0) (σ X0)
       have i₂ := eq191639 X0
       grind)
    | exact superpose eq191639 eq18
    | exact resolve eq18 eq191639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq197432 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq192764 y X0
       have i₂ := eq144239
       grind)
    | exact superpose eq144239 eq192764
    | exact resolve eq192764 eq144239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192764
  have eq198065 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ (k X0 y)) (σ X0)) ∨ (k y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq197432 (σ X0)
       have i₂ := eq142181 X0 y
       grind)
    | exact superpose eq142181 eq197432
    | (have j1 := eq142181 X0 y
       grind)
    | exact resolve eq197432 eq142181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198610 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ (k X0 y)) (σ X0)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq198065 X0
       have i₂ := eq146445
       grind)
    | exact superpose eq146445 eq198065
    | (have j0 := eq198065 X0
       grind)
    | exact resolve eq198065 eq146445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146445 eq198065
  have eq199065 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq192862 y X0
       have i₂ := eq144239
       grind)
    | exact superpose eq144239 eq192862
    | exact resolve eq192862 eq144239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144239 eq192862
  have eq199960 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq197432 x
       have i₂ := eq199065 x
       grind)
    | exact superpose eq199065 eq197432
    | exact resolve eq197432 eq199065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197432 eq199065
  have eq200848 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq355 y x
       have i₂ := eq199960
       grind)
    | exact superpose eq199960 eq355
    | (have j0 := eq355 y x
       grind)
    | exact resolve eq355 eq199960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq200859 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq142181 y x
       have i₂ := eq199960
       grind)
    | exact superpose eq199960 eq142181
    | (have j0 := eq142181 y x
       grind)
    | exact resolve eq142181 eq199960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142181
  have eq200986 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq200859
       have i₂ := eq191175 x
       grind)
    | exact superpose eq191175 eq200859
    | exact resolve eq200859 eq191175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191175 eq200859
  have eq206825 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq200848
       grind)
    | exact superpose eq200848 eq14
    | exact resolve eq14 eq200848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200848
  have eq206905 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq206825
       have i₂ := eq1480 y x
       grind)
    | exact superpose eq1480 eq206825
    | (have j1 := eq1480 y x
       grind)
    | exact resolve eq206825 eq1480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1480 eq206825
  have eq206910 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = (k y x) := by grind
  clear eq206905
  have eq206915 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq206910
       have i₂ := eq144424
       grind)
    | exact superpose eq144424 eq206910
    | exact resolve eq206910 eq144424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206910
  have eq206916 : x = (k y x) := by grind
  clear eq206915
  have eq206960 : (σ x) = (σ (M.op y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1228 y x
       have i₂ := eq206916
       grind)
    | exact superpose eq206916 eq1228
    | (have j0 := eq1228 y x
       grind)
    | exact resolve eq1228 eq206916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228
  have eq206994 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq206960
       have i₂ := eq144424
       grind)
    | exact superpose eq144424 eq206960
    | exact resolve eq206960 eq144424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144424 eq206960
  have eq212257 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq200986
       grind)
    | exact superpose eq200986 eq14
    | exact resolve eq14 eq200986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200986
  have eq212298 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq212257
       have i₂ := eq206916
       grind)
    | exact superpose eq206916 eq212257
    | exact resolve eq212257 eq206916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206916 eq212257
  have eq212313 : y = (M.op x x) := by
    first
    | (have r₁ := eq212298
       have r₂ := eq206994
       grind)
    | exact resolve eq212298 eq206994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206994 eq212298
  have eq212346 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op x y) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq19 x X0
       have i₂ := eq212313
       grind)
    | exact superpose eq212313 eq19
    | exact resolve eq19 eq212313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212617 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq19 x x
       have i₂ := eq212313
       grind)
    | exact superpose eq212313 eq19
    | exact resolve eq19 eq212313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq218148 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op (M.op x y) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq144434 X0
       have i₂ := eq212346 X0
       grind)
    | exact superpose eq212346 eq144434
    | exact resolve eq144434 eq212346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212346
  have eq242975 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ (M.op X0 y)) (σ X0)) ∨ x = X0 ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq198610 X0
       have i₂ := eq171570 X0
       grind)
    | exact superpose eq171570 eq198610
    | (have j0 := eq198610 X0
       have j1 := eq171570 X0
       grind)
    | exact resolve eq198610 eq171570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171570 eq198610
  have eq243013 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ (M.op X0 y)) (σ X0)) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq242975 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242975
  have eq243052 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (M.op X0 y)) (σ X0)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq243013 X0
       have i₂ := eq199960
       grind)
    | exact superpose eq199960 eq243013
    | (have j0 := eq243013 X0
       grind)
    | exact resolve eq243013 eq199960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199960 eq243013
  have eq253620 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq243052 (M.op x y)
       have i₂ := eq212617
       grind)
    | exact superpose eq212617 eq243052
    | (have j0 := eq243052 (M.op x y)
       grind)
    | exact resolve eq243052 eq212617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212617 eq243052
  have eq253672 : (M.op (σ x) (σ y)) = (σ (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq253620
       have i₂ := eq191639 (M.op x y)
       grind)
    | exact superpose eq191639 eq253620
    | exact resolve eq253620 eq191639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253620
  have eq253675 : (M.op (σ x) (σ y)) = (σ (M.op x (M.op x x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq253672
       have i₂ := eq144434 x
       grind)
    | exact superpose eq144434 eq253672
    | exact resolve eq253672 eq144434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144434 eq253672
  have eq253677 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq253675
       have i₂ := eq212313
       grind)
    | exact superpose eq212313 eq253675
    | exact resolve eq253675 eq212313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253675
  have eq253679 : x = (M.op x y) := by
    first
    | (have r₁ := eq253677
       have r₂ := eq14
       grind)
    | exact resolve eq253677 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253677
  have eq253833 : (M.op x x) = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq218148 x
       have i₂ := eq253679
       grind)
    | exact superpose eq253679 eq218148
    | exact resolve eq218148 eq253679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218148
  have eq254856 : y = (M.op x y) := by
    first
    | (have i₁ := eq253833
       have i₂ := eq212313
       grind)
    | exact superpose eq212313 eq253833
    | exact resolve eq253833 eq212313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212313 eq253833
  have eq255289 : x = y := by
    first
    | (have i₁ := eq254856
       have i₂ := eq253679
       grind)
    | exact superpose eq253679 eq254856
    | exact resolve eq254856 eq253679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253679 eq254856
  have eq256650 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq255289
       grind)
    | exact superpose eq255289 eq14
    | exact resolve eq14 eq255289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255289
  have eq257140 : False := by grind
  exact eq257140

/-- `Equation4388`: `x ◇ (x ◇ x) = (y ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pxy_Equation4388 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4388 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4388.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
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
  have eq18 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X2 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq8 X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq26 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X1)) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X1) = (M.op X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq30 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq33 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq23
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq23 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq84 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq101 : ∀ X0 X1 X2 : G, (k X2 X1) = (M.op X2 X1) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26 X0 X0 X2
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq26 X0 X1 X2
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq26
    | (have j0 := eq26 X1 X1 X2
       have j1 := eq12 X2 X1
       grind)
    | exact resolve eq26 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq158 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 x
       have i₂ := eq27 X1 X0 x
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq27 X0 (M.op X1 X1) x
       grind)
    | exact superpose eq27 eq8
    | (have j1 := eq27 X1 X0 x
       grind)
    | exact resolve eq8 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (M.op X2 X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq27 (σ X1) (σ X0) X2
       grind)
    | exact superpose eq27 eq13
    | (have j1 := eq27 (σ X1) (σ X0) X2
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq294 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq30 x y
       grind)
    | exact superpose eq30 eq14
    | (have j1 := eq30 x y
       grind)
    | exact resolve eq14 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq309 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq9
    | (have j1 := eq30 X0 X1
       grind)
    | exact resolve eq9 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq311 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (σ X1) (M.op (σ X0) (σ X0))) ∨ (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq30 X0 X2
       grind)
    | exact superpose eq30 eq13
    | (have j1 := eq30 X0 X2
       grind)
    | exact resolve eq13 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq331 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq30 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq800 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq33
    | exact resolve eq33 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq876 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq800 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq800
    | (have j0 := eq800 X0 X1
       grind)
    | exact resolve eq800 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800
  have eq932 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq1929 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq294
       have i₂ := eq932 y x
       grind)
    | exact superpose eq932 eq294
    | (have j1 := eq932 y x
       grind)
    | (have r₁ := eq294
       have r₂ := eq932 y x
       grind)
    | exact resolve eq294 eq932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932
  have eq1930 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq294
       have i₂ := eq876 y x
       grind)
    | exact superpose eq876 eq294
    | (have j1 := eq876 (σ y) (σ x)
       grind)
    | (have r₁ := eq294
       have r₂ := eq876 y x
       grind)
    | exact resolve eq294 eq876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq1931 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1930
  have eq1932 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x y) := by grind
  clear eq1929
  have eq1943 : (τ (σ y)) = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq90 x
       have i₂ := eq1931
       grind)
    | exact superpose eq1931 eq90
    | exact resolve eq90 eq1931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1968 : y = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1943
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1943
    | exact resolve eq1943 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1943
  have eq2011 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq309 x x
       have i₂ := eq1931
       grind)
    | exact superpose eq1931 eq309
    | exact resolve eq309 eq1931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq2040 : (σ y) = (σ (k x x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2011
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2011
    | exact resolve eq2011 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2011
  have eq2058 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq876 y x
       have i₂ := eq1968
       grind)
    | exact superpose eq1968 eq876
    | (have j0 := eq876 y x
       grind)
    | exact resolve eq876 eq1968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876 eq1968
  have eq2059 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq2058
  have eq2646 : (τ (σ y)) = (k x (τ (σ y))) ∨ y = (k x y) := by
    first
    | (have i₁ := eq90 x
       have i₂ := eq1932
       grind)
    | exact superpose eq1932 eq90
    | exact resolve eq90 eq1932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1932
  have eq2677 : y = (k x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq2646
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2646
    | exact resolve eq2646 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2646
  have eq2678 : y = (k x y) := by grind
  clear eq2677
  have eq2872 : ∀ X0 : G, y = (M.op x y) ∨ (k X0 x) = (M.op X0 x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq101 y x X0
       have i₂ := eq2678
       grind)
    | exact superpose eq2678 eq101
    | (have j0 := eq101 y x X0
       grind)
    | exact resolve eq101 eq2678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq2678
  have eq2874 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2872 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2872
  have eq3227 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op (τ X0) x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x
       have i₂ := eq2874 (τ X0)
       grind)
    | exact superpose eq2874 eq16
    | exact resolve eq16 eq2874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq2874
  have eq11467 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) ≠ (M.op (M.op X2 X2) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq187 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq11959 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq2040
       grind)
    | exact superpose eq2040 eq9
    | exact resolve eq9 eq2040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040
  have eq12015 : y = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11959
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq11959
    | exact resolve eq11959 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11959
  have eq12389 : y = (M.op x x) ∨ x = y ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq12015
       grind)
    | exact superpose eq12015 eq28
    | exact resolve eq28 eq12015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq12015
  have eq12409 : y = (M.op x x) ∨ x = y := by grind
  clear eq12389
  have eq12673 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq8 X0 x
       have i₂ := eq12409
       grind)
    | exact superpose eq12409 eq8
    | exact resolve eq8 eq12409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13142 : (M.op x y) = (M.op y x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq12673 x
       have i₂ := eq12409
       grind)
    | exact superpose eq12409 eq12673
    | exact resolve eq12673 eq12409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12673
  have eq13241 : (M.op x y) = (M.op y x) ∨ x = y := by grind
  clear eq13142
  have eq14849 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  clear eq311
  have eq30652 : ∀ X0 : G, (σ (M.op X0 x)) = (k (σ X0) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3227 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq3227
    | exact resolve eq3227 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3227
  have eq30768 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op X0 x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq30652 X0
       have i₂ := eq13 X0 x
       grind)
    | exact superpose eq13 eq30652
    | exact resolve eq30652 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30652
  have eq45650 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 (τ (σ X0))) ∨ (k (τ (σ X1)) X0) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0
       have i₂ := eq72 (σ X0) X1
       grind)
    | exact superpose eq72 eq90
    | (have j1 := eq72 (σ X1) X0
       grind)
    | exact resolve eq90 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq90
  have eq45860 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k (τ (σ X1)) X0) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq45650 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq45650
    | (have j0 := eq45650 X0 X1
       grind)
    | exact resolve eq45650 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45650
  have eq45983 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq45860 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq45860
    | (have j0 := eq45860 X0 X1
       grind)
    | exact resolve eq45860 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45860
  have eq49747 : (k x x) = (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq45983 x x
       have i₂ := eq1931
       grind)
    | exact superpose eq1931 eq45983
    | (have j0 := eq45983 x x
       grind)
    | exact resolve eq45983 eq1931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45983
  have eq49851 : y = (k x x) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq49747
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq49747
    | exact resolve eq49747 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49747
  have eq57387 : x ≠ y ∨ x = (k x x) ∨ y = (M.op x x) := by grind
  clear eq49851
  have eq57423 : x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq57387
       have r₂ := eq12409
       grind)
    | exact resolve eq57387 eq12409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57387
  have eq58863 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq331 x
       have i₂ := eq57423
       grind)
    | exact superpose eq57423 eq331
    | (have j0 := eq331 x
       grind)
    | exact resolve eq331 eq57423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331 eq57423
  have eq58890 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq58863
  have eq64872 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ x) X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq8 X0 (σ x)
       have i₂ := eq58890
       grind)
    | exact superpose eq58890 eq8
    | exact resolve eq8 eq58890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58890
  have eq124398 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq64872 (σ x)
       have i₂ := eq1931
       grind)
    | exact superpose eq1931 eq64872
    | exact resolve eq64872 eq1931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1931 eq64872
  have eq124521 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq124398
  have eq124563 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq124521
       grind)
    | exact superpose eq124521 eq14
    | exact resolve eq14 eq124521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124521
  have eq124588 : y = (M.op x x) := by
    first
    | (have r₁ := eq124563
       have r₂ := eq2059
       grind)
    | exact resolve eq124563 eq2059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2059 eq124563
  have eq124598 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq8 X0 x
       have i₂ := eq124588
       grind)
    | exact superpose eq124588 eq8
    | exact resolve eq8 eq124588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124601 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 x
       have i₂ := eq124588
       grind)
    | exact superpose eq124588 eq18
    | exact resolve eq18 eq124588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq124958 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq124598 x
       have i₂ := eq124588
       grind)
    | exact superpose eq124588 eq124598
    | exact resolve eq124598 eq124588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126286 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq14849 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126287 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq126286 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126286
  have eq126348 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq126287 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq126287
    | exact resolve eq126287 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126578 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (M.op y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq124598 (σ X0)
       have i₂ := eq126287 X0
       grind)
    | exact superpose eq126287 eq124598
    | exact resolve eq124598 eq126287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126579 : ∀ X0 X1 : G, (M.op (σ (k X0 X0)) X1) = (M.op y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq124601 (σ X0) X1
       have i₂ := eq126287 X0
       grind)
    | exact superpose eq126287 eq124601
    | exact resolve eq124601 eq126287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126753 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq126348 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq126348
    | exact resolve eq126348 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126348
  have eq126811 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq126753 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq126753
    | exact resolve eq126753 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126753
  have eq128066 : ∀ X0 X1 : G, (M.op y X1) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq126579 X0 X1
       have i₂ := eq126811 X0
       grind)
    | exact superpose eq126811 eq126579
    | exact resolve eq126579 eq126811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126579
  have eq130488 : ∀ X0 : G, (M.op y X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq128066 x X0
       have i₂ := eq124588
       grind)
    | exact superpose eq124588 eq128066
    | exact resolve eq128066 eq124588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130491 : ∀ X0 : G, (M.op y X0) = (M.op (σ y) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq128066 x X0
       have i₂ := eq12409
       grind)
    | exact superpose eq12409 eq128066
    | exact resolve eq128066 eq12409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12409 eq128066
  have eq131225 : (σ (k y y)) = (M.op y (σ y)) := by
    first
    | (have i₁ := eq126287 y
       have i₂ := eq130488 (σ y)
       grind)
    | exact superpose eq130488 eq126287
    | exact resolve eq126287 eq130488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126287
  have eq131369 : ∀ X0 : G, (M.op y X0) ≠ X0 ∨ (k (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq84 (σ y) X0
       have i₂ := eq130488 X0
       grind)
    | exact superpose eq130488 eq84
    | (have j0 := eq84 y X0
       grind)
    | exact resolve eq84 eq130488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq131580 : (M.op y (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq131225
       have i₂ := eq126811 y
       grind)
    | exact superpose eq126811 eq131225
    | exact resolve eq131225 eq126811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131225
  have eq137654 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op y (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11467 X0 X1 x
       have i₂ := eq124601 x (σ X0)
       grind)
    | exact superpose eq124601 eq11467
    | (have j0 := eq11467 X0 X1 x
       grind)
    | exact resolve eq11467 eq124601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11467 eq124601
  have eq137776 : ∀ X0 : G, (σ (k y X0)) = (M.op y (σ y)) ∨ (M.op (σ y) (σ X0)) = (σ (k y X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq14849 y X0
       have i₂ := eq130491 (σ y)
       grind)
    | exact superpose eq130491 eq14849
    | (have j0 := eq14849 y X0
       grind)
    | exact resolve eq14849 eq130491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14849 eq130491
  have eq138041 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (k y X0)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq137776 X0
       have j1 := eq137654 y X0
       grind)
    | (have r₁ := eq137776 x
       have r₂ := eq137654 y x
       grind)
    | exact resolve eq137776 eq137654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137654 eq137776
  have eq138138 : ∀ X0 : G, (σ (k y X0)) = (M.op y (σ X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq138041 X0
       have i₂ := eq130488 (σ X0)
       grind)
    | exact superpose eq130488 eq138041
    | exact resolve eq138041 eq130488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130488 eq138041
  have eq139114 : ∀ X0 : G, (M.op y (M.op y y)) ≠ X0 ∨ (k (σ y) X0) = X0 ∨ (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq131369 X0
       have i₂ := eq158 y X0
       grind)
    | (have i₁ := eq131369 (M.op y y)
       have i₂ := eq158 y x
       grind)
    | exact superpose eq158 eq131369
    | (have j0 := eq131369 X0
       have j1 := eq158 y X0
       grind)
    | (have r₁ := eq131369 (M.op y y)
       have r₂ := eq158 y y
       grind)
    | (have r₁ := eq131369 (M.op y (M.op y y))
       have r₂ := eq158 y (M.op y (M.op y y))
       grind)
    | exact resolve eq131369 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158 eq131369
  have eq139131 : ∀ X0 : G, (M.op y y) ≠ X0 ∨ (k (σ y) X0) = X0 ∨ (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq139114 X0
       have i₂ := eq124598 y
       grind)
    | exact superpose eq124598 eq139114
    | (have j0 := eq139114 X0
       grind)
    | (have r₁ := eq139114 (M.op y y)
       have r₂ := eq124598 y
       grind)
    | (have r₁ := eq139114 (M.op (M.op y y) (M.op (M.op y y) (M.op y y)))
       have r₂ := eq124598 (M.op y y)
       grind)
    | exact resolve eq139114 eq124598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124598 eq139114
  have eq139135 : ∀ X0 : G, (k (σ y) X0) = X0 ∨ (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq139131 X0
       have j1 := eq12 y X0
       grind)
    | (have r₁ := eq139131 x
       have r₂ := eq12 y x
       grind)
    | (have r₁ := eq139131 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op y y)
       grind)
    | (have r₁ := eq139131 (k y y)
       have r₂ := eq12 y y
       grind)
    | exact resolve eq139131 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139131
  have eq143468 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq126578 X0
       have i₂ := eq126811 X0
       grind)
    | exact superpose eq126811 eq126578
    | exact resolve eq126578 eq126811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126578 eq126811
  have eq145341 : (M.op (σ x) (σ y)) = (M.op y (σ x)) := by
    first
    | (have i₁ := eq143468 x
       have i₂ := eq124588
       grind)
    | exact superpose eq124588 eq143468
    | exact resolve eq143468 eq124588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143468
  have eq145709 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq145341
       grind)
    | exact superpose eq145341 eq14
    | exact resolve eq14 eq145341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145341
  have eq153384 : ∀ X0 : G, (k (σ y) X0) = (M.op y (σ (τ X0))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq17 X0 y
       have i₂ := eq138138 (τ X0)
       grind)
    | exact superpose eq138138 eq17
    | exact resolve eq17 eq138138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153392 : (M.op y (σ x)) = (σ (M.op y x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq30768 y
       have i₂ := eq138138 x
       grind)
    | exact superpose eq138138 eq30768
    | exact resolve eq30768 eq138138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30768
  have eq153421 : (σ (M.op x y)) = (M.op y (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq153392
       have i₂ := eq124958
       grind)
    | exact superpose eq124958 eq153392
    | exact resolve eq153392 eq124958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153392
  have eq153429 : ∀ X0 : G, (M.op y X0) = (k (σ y) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq153384 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq153384
    | exact resolve eq153384 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153384
  have eq153471 : y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq153421
       have r₂ := eq145709
       grind)
    | exact resolve eq153421 eq145709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153421
  have eq154437 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op y X0)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq38 y X0
       have i₂ := eq153429 X0
       grind)
    | exact superpose eq153429 eq38
    | exact resolve eq38 eq153429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq153429
  have eq155518 : (τ (M.op x y)) = (k y (τ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq154437 x
       have i₂ := eq13241
       grind)
    | exact superpose eq13241 eq154437
    | exact resolve eq154437 eq13241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13241 eq154437
  have eq155594 : (τ (M.op x y)) = (k y (τ x)) ∨ x = y := by grind
  clear eq155518
  have eq155917 : (τ y) = (k y (τ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq155594
       have i₂ := eq153471
       grind)
    | exact superpose eq153471 eq155594
    | exact resolve eq155594 eq153471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153471 eq155594
  have eq155935 : (τ y) = (k y (τ x)) ∨ x = y := by grind
  clear eq155917
  have eq156104 : (σ (τ y)) = (k (σ y) x) ∨ x = y := by
    first
    | (have i₁ := eq17 x y
       have i₂ := eq155935
       grind)
    | exact superpose eq155935 eq17
    | exact resolve eq17 eq155935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq155935
  have eq156159 : y = (k (σ y) x) ∨ x = y := by
    first
    | (have i₁ := eq156104
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq156104
    | exact resolve eq156104 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156104
  have eq172397 : x = y ∨ x = y ∨ (M.op y x) = (k y x) := by
    first
    | (have i₁ := eq156159
       have i₂ := eq139135 x
       grind)
    | exact superpose eq139135 eq156159
    | (have j1 := eq139135 x
       grind)
    | exact resolve eq156159 eq139135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139135 eq156159
  have eq172433 : x = y ∨ (M.op y x) = (k y x) := by grind
  clear eq172397
  have eq172454 : (M.op x y) = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq172433
       have i₂ := eq124958
       grind)
    | exact superpose eq124958 eq172433
    | exact resolve eq172433 eq124958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124958 eq172433
  have eq172504 : (σ (M.op x y)) = (M.op y (σ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq138138 x
       have i₂ := eq172454
       grind)
    | exact superpose eq172454 eq138138
    | exact resolve eq138138 eq172454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138138 eq172454
  have eq172528 : (σ (M.op x y)) = (M.op y (σ x)) ∨ x = y := by grind
  clear eq172504
  have eq172532 : x = y := by
    first
    | (have r₁ := eq172528
       have r₂ := eq145709
       grind)
    | exact resolve eq172528 eq145709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172528
  have eq172628 : (σ (M.op x x)) = (M.op x (σ x)) := by
    first
    | (have i₁ := eq131580
       have i₂ := eq172532
       grind)
    | exact superpose eq172532 eq131580
    | exact resolve eq131580 eq172532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131580
  have eq172681 : (σ (M.op x x)) ≠ (M.op x (σ x)) := by
    first
    | (have i₁ := eq145709
       have i₂ := eq172532
       grind)
    | exact superpose eq172532 eq145709
    | exact resolve eq145709 eq172532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145709
  have eq172708 : (σ y) ≠ (M.op x (σ x)) := by
    first
    | (have i₁ := eq172681
       have i₂ := eq124588
       grind)
    | exact superpose eq124588 eq172681
    | exact resolve eq172681 eq124588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172681
  have eq172734 : (σ y) = (M.op x (σ x)) := by
    first
    | (have i₁ := eq172628
       have i₂ := eq124588
       grind)
    | exact superpose eq124588 eq172628
    | exact resolve eq172628 eq124588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124588 eq172628
  have eq172777 : (σ x) ≠ (M.op x (σ x)) := by
    first
    | (have i₁ := eq172708
       have i₂ := eq172532
       grind)
    | exact superpose eq172532 eq172708
    | exact resolve eq172708 eq172532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172708
  have eq172795 : (σ x) = (M.op x (σ x)) := by
    first
    | (have i₁ := eq172734
       have i₂ := eq172532
       grind)
    | exact superpose eq172532 eq172734
    | exact resolve eq172734 eq172532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172532 eq172734
  have eq172818 : False := by grind
  exact eq172818

/-- `Equation4388`: `x ◇ (x ◇ x) = (y ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation4388 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4388 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4388.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq18 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X2 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq8 X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq24 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq20 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq20
    | exact resolve eq20 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq29 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
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
  have eq34 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X1) (M.op (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1
    grind
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq29
    | exact resolve eq29 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq29 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq90 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1
       have i₂ := eq12 (τ X1) X0
       grind)
    | (have i₁ := eq24 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq24
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq24 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq133 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq39
  have eq148 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq133 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq133
    | exact resolve eq133 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq281 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq148 X1
       have i₂ := eq12 (σ X1) X0
       grind)
    | (have i₁ := eq148 X0
       have i₂ := eq12 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq12 eq148
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq148 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq318 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq31 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq31
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq31 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq333 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq338 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq347 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq9
    | (have j1 := eq31 X0 X1
       grind)
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq370 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq31 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq379 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq338 X0
       have i₂ := eq13 X0 (k X0 X0)
       grind)
    | exact superpose eq13 eq338
    | (have j0 := eq338 X0
       grind)
    | exact resolve eq338 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq953 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq34
    | exact resolve eq34 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq1042 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq953 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq953
    | (have j0 := eq953 X0 X1
       grind)
    | exact resolve eq953 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953
  have eq1107 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq2014 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq14
    | (have j1 := eq79 x y
       grind)
    | exact resolve eq14 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2015 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X1
       have i₂ := eq79 X0 X0
       grind)
    | exact superpose eq79 eq31
    | (have j0 := eq31 X0 X1
       have j1 := eq79 X0 X1
       grind)
    | exact resolve eq31 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq2018 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (σ X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X0) X1
       have i₂ := eq79 X0 X0
       grind)
    | exact superpose eq79 eq8
    | (have j1 := eq79 X0 X0
       grind)
    | exact resolve eq8 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2020 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq79 X0 X0
       grind)
    | exact superpose eq79 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq79 X0 X0
       grind)
    | exact resolve eq12 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq2282 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq333
       have i₂ := eq1107 y x
       grind)
    | exact superpose eq1107 eq333
    | (have j1 := eq1107 y x
       grind)
    | (have r₁ := eq333
       have r₂ := eq1107 y x
       grind)
    | exact resolve eq333 eq1107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107
  have eq2283 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq333
       have i₂ := eq1042 y x
       grind)
    | exact superpose eq1042 eq333
    | (have j1 := eq1042 (σ y) (σ x)
       grind)
    | (have r₁ := eq333
       have r₂ := eq1042 y x
       grind)
    | exact resolve eq333 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq2284 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq2283
  have eq2285 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq2282
  have eq2295 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq148 x
       have i₂ := eq2284
       grind)
    | exact superpose eq2284 eq148
    | exact resolve eq148 eq2284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2317 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq85 (σ x) (σ x)
       have i₂ := eq2284
       grind)
    | exact superpose eq2284 eq85
    | (have j0 := eq85 (σ x) (σ x)
       grind)
    | exact resolve eq85 eq2284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq2319 : (σ x) = (σ (k x x)) ∨ (σ x) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2317
       have i₂ := eq13 x x
       grind)
    | exact superpose eq13 eq2317
    | exact resolve eq2317 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2317
  have eq2322 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2295
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2295
    | exact resolve eq2295 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2295
  have eq2407 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1042 y x
       have i₂ := eq2322
       grind)
    | exact superpose eq2322 eq1042
    | (have j0 := eq1042 y x
       grind)
    | exact resolve eq1042 eq2322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042 eq2322
  have eq2408 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq2407
  have eq3261 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq148 x
       have i₂ := eq2285
       grind)
    | exact superpose eq2285 eq148
    | exact resolve eq148 eq2285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq2285
  have eq3296 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq3261
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3261
    | exact resolve eq3261 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3261
  have eq3297 : x = (k x y) := by grind
  clear eq3296
  have eq4199 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq90
    | (have j0 := eq90 X1 (σ X0)
       grind)
    | exact resolve eq90 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq4274 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4199 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq4199
    | (have j0 := eq4199 X0 X1
       grind)
    | exact resolve eq4199 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4199
  have eq12744 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 (τ (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X0) X1
       have i₂ := eq281 (σ X1) X0
       grind)
    | exact superpose eq281 eq23
    | (have j1 := eq281 (σ X1) X0
       grind)
    | exact resolve eq23 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq12774 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 (τ (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12744 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq12744
    | (have j0 := eq12744 X0 X1
       grind)
    | exact resolve eq12744 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12744
  have eq12813 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12774 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq12774
    | (have j0 := eq12774 X0 X1
       grind)
    | exact resolve eq12774 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12774
  have eq33983 : (k x x) = (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12813 x x
       have i₂ := eq2284
       grind)
    | exact superpose eq2284 eq12813
    | (have j0 := eq12813 x x
       grind)
    | exact resolve eq12813 eq2284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12813
  have eq34072 : y = (k x x) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq33983
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq33983
    | exact resolve eq33983 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33983
  have eq42409 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4274 x x
       have i₂ := eq34072
       grind)
    | exact superpose eq34072 eq4274
    | exact resolve eq4274 eq34072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4274 eq34072
  have eq42413 : x = (k x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq42409
  have eq53884 : (σ x) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq379 x
       have i₂ := eq42413
       grind)
    | exact superpose eq42413 eq379
    | (have j0 := eq379 x
       grind)
    | exact resolve eq379 eq42413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379 eq42413
  have eq53921 : (σ x) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq53884
       have r₂ := eq2319
       grind)
    | exact resolve eq53884 eq2319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2319 eq53884
  have eq53925 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq370 x
       grind)
    | (have r₁ := eq53921
       have r₂ := eq370 x
       grind)
    | exact resolve eq53921 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53921
  have eq55078 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2284
       have i₂ := eq53925
       grind)
    | exact superpose eq53925 eq2284
    | exact resolve eq2284 eq53925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55098 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ x) X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq8 X0 (σ x)
       have i₂ := eq53925
       grind)
    | exact superpose eq53925 eq8
    | exact resolve eq8 eq53925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53925
  have eq55174 : y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq55078
  have eq56135 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y X0) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq8 X0 x
       have i₂ := eq55174
       grind)
    | exact superpose eq55174 eq8
    | exact resolve eq8 eq55174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59605 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq56135 x
       have i₂ := eq55174
       grind)
    | exact superpose eq55174 eq56135
    | exact resolve eq56135 eq55174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56135
  have eq59670 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq59605
  have eq65106 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq55098 (σ x)
       have i₂ := eq2284
       grind)
    | exact superpose eq2284 eq55098
    | exact resolve eq55098 eq2284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2284 eq55098
  have eq65218 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq65106
  have eq65255 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq65218
       grind)
    | exact superpose eq65218 eq14
    | exact resolve eq14 eq65218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65218
  have eq65315 : (σ x) ≠ (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq65255
       have i₂ := eq2408
       grind)
    | exact superpose eq2408 eq65255
    | exact resolve eq65255 eq2408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2408 eq65255
  have eq65317 : (σ x) ≠ (σ y) ∨ y = (M.op x x) := by grind
  clear eq65315
  have eq65319 : y = (M.op x x) := by
    first
    | (have r₁ := eq65317
       have r₂ := eq55174
       grind)
    | exact resolve eq65317 eq55174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55174 eq65317
  have eq65358 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq8 X0 x
       have i₂ := eq65319
       grind)
    | exact superpose eq65319 eq8
    | exact resolve eq8 eq65319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65361 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1 x
       have i₂ := eq65319
       grind)
    | exact superpose eq65319 eq18
    | exact resolve eq18 eq65319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq65375 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op y (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq68 x X0
       have i₂ := eq65319
       grind)
    | exact superpose eq65319 eq68
    | exact resolve eq68 eq65319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq71262 : (M.op y y) = (k (M.op y y) (M.op y y)) := by
    first
    | (have i₁ := eq65375 y
       have i₂ := eq65358 y
       grind)
    | exact superpose eq65358 eq65375
    | exact resolve eq65375 eq65358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65358 eq65375
  have eq71319 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
    first
    | (have i₁ := eq370 (M.op y y)
       have i₂ := eq71262
       grind)
    | exact superpose eq71262 eq370
    | (have j0 := eq370 (M.op y y)
       grind)
    | exact resolve eq370 eq71262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71349 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by grind
  clear eq71319
  have eq75336 : ∀ X0 : G, (τ (σ (M.op y y))) = X0 ∨ (σ (k (M.op y y) X0)) = (M.op (σ (M.op y y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq347 (M.op y y) X0
       have i₂ := eq71349
       grind)
    | exact superpose eq71349 eq347
    | (have j0 := eq347 (M.op y y) X0
       grind)
    | exact resolve eq347 eq71349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq75474 : ∀ X0 : G, (M.op y X0) = (M.op (σ (M.op y y)) X0) := by
    intro X0
    first
    | (have i₁ := eq65361 (σ (M.op y y)) X0
       have i₂ := eq71349
       grind)
    | exact superpose eq71349 eq65361
    | exact resolve eq65361 eq71349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75611 : ∀ X0 : G, (M.op y y) = X0 ∨ (σ (k (M.op y y) X0)) = (M.op (σ (M.op y y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq75336 X0
       have i₂ := eq9 (M.op y y)
       grind)
    | exact superpose eq9 eq75336
    | (have j0 := eq75336 X0
       grind)
    | exact resolve eq75336 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75336
  have eq75673 : ∀ X0 : G, (M.op y (σ X0)) = (σ (k (M.op y y) X0)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq75611 X0
       have i₂ := eq75474 (σ X0)
       grind)
    | exact superpose eq75474 eq75611
    | (have j0 := eq75611 X0
       grind)
    | exact resolve eq75611 eq75474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75474 eq75611
  have eq78200 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq2020 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2020
  have eq78201 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq78200 X0 X1
       have j1 := eq318 X1 X0
       grind)
    | (have r₁ := eq78200 (k X1 X1) X0
       have r₂ := eq318 X0 X1
       grind)
    | (have r₁ := eq78200 X0 (σ (k X1 X1))
       have r₂ := eq318 (σ X0) X1
       grind)
    | (have r₁ := eq78200 X1 X0
       have r₂ := eq318 X0 X1
       grind)
    | exact resolve eq78200 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318 eq78200
  have eq78248 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq78201 (τ X1) X0
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq78201 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq78201 eq16
    | (have j1 := eq78201 (τ X1) X0
       grind)
    | exact resolve eq16 eq78201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq78249 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq78201 X1 X0
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq78201 X0 (σ X0)
       grind)
    | exact superpose eq78201 eq9
    | (have j1 := eq78201 X1 X0
       grind)
    | exact resolve eq9 eq78201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78201
  have eq78268 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq78248 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq78248
    | (have j0 := eq78248 X0 X1
       grind)
    | exact resolve eq78248 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78248
  have eq78277 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq78268 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq78268
    | (have j0 := eq78268 X0 X1
       grind)
    | exact resolve eq78268 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78268
  have eq78432 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq78277 (τ X1) X0
       grind)
    | exact superpose eq78277 eq17
    | (have j1 := eq78277 (τ X1) X0
       grind)
    | exact resolve eq17 eq78277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq78472 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq2014
       have i₂ := eq78277 y x
       grind)
    | exact superpose eq78277 eq2014
    | (have j1 := eq78277 y x
       grind)
    | exact resolve eq2014 eq78277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2014 eq78277
  have eq78599 : (σ (M.op x y)) = (σ x) ∨ y = (k x x) := by grind
  clear eq78472
  have eq80736 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq78249 (σ X1) X0
       grind)
    | exact superpose eq78249 eq13
    | (have j1 := eq78249 (σ X1) X0
       grind)
    | exact resolve eq13 eq78249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80740 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X0) X1
       have i₂ := eq78249 (σ X1) X0
       grind)
    | exact superpose eq78249 eq23
    | (have j1 := eq78249 (σ X1) X0
       grind)
    | exact resolve eq23 eq78249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq78249
  have eq80742 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq80740 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq80740
    | (have j0 := eq80740 X0 X1
       grind)
    | exact resolve eq80740 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80740
  have eq80744 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq80736 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq80736
    | (have j0 := eq80736 X0 X1
       grind)
    | exact resolve eq80736 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80736
  have eq80773 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq80742 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq80742
    | (have j0 := eq80742 X0 X1
       grind)
    | exact resolve eq80742 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80742
  have eq81732 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq80744 x y
       grind)
    | exact superpose eq80744 eq14
    | (have j1 := eq80744 x y
       grind)
    | exact resolve eq14 eq80744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80744
  have eq81816 : (σ (M.op x y)) ≠ (σ x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq81732
       have i₂ := eq3297
       grind)
    | exact superpose eq3297 eq81732
    | exact resolve eq81732 eq3297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3297 eq81732
  have eq81838 : y = (k x x) := by
    first
    | (have r₁ := eq81816
       have r₂ := eq78599
       grind)
    | exact resolve eq81816 eq78599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78599 eq81816
  have eq81911 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq370 x
       have i₂ := eq81838
       grind)
    | exact superpose eq81838 eq370
    | (have j0 := eq370 x
       grind)
    | exact resolve eq370 eq81838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq81925 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 X0) (σ x)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq2018 x x
       have i₂ := eq81838
       grind)
    | exact superpose eq81838 eq2018
    | exact resolve eq2018 eq81838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2018
  have eq82005 : (M.op (σ x) (σ y)) = (M.op y (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq81925 x
       have i₂ := eq65361 x (σ x)
       grind)
    | exact superpose eq65361 eq81925
    | exact resolve eq81925 eq65361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81925
  have eq88307 : (σ (M.op x y)) ≠ (M.op y (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq82005
       grind)
    | exact superpose eq82005 eq14
    | exact resolve eq14 eq82005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82005
  have eq108866 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq78432 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq78432
    | exact resolve eq78432 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78432
  have eq108935 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq108866 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq108866
    | (have j0 := eq108866 X0 X1
       grind)
    | exact resolve eq108866 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108866
  have eq109103 : ∀ X0 : G, (M.op y y) = X0 ∨ (σ (k (M.op y y) X0)) = (σ (M.op (M.op y y) X0)) := by
    intro X0
    first
    | (have i₁ := eq71262
       have i₂ := eq108935 X0 (M.op y y)
       grind)
    | (have i₁ := eq71262
       have i₂ := eq108935 (k (M.op y y) (M.op y y)) x
       grind)
    | exact superpose eq108935 eq71262
    | (have j1 := eq108935 X0 (M.op y y)
       grind)
    | exact resolve eq71262 eq108935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71262 eq108935
  have eq109117 : ∀ X0 : G, (σ (M.op y X0)) = (σ (k (M.op y y) X0)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq109103 X0
       have i₂ := eq65361 y X0
       grind)
    | exact superpose eq65361 eq109103
    | (have j0 := eq109103 X0
       grind)
    | exact resolve eq109103 eq65361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65361 eq109103
  have eq118141 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op y X0)) ∨ (M.op y y) = X0 ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq109117 X0
       have i₂ := eq75673 X0
       grind)
    | exact superpose eq75673 eq109117
    | (have j0 := eq109117 X0
       have j1 := eq75673 X0
       grind)
    | exact resolve eq109117 eq75673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75673 eq109117
  have eq118152 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op y X0)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have j0 := eq118141 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118141
  have eq118182 : (σ (M.op x y)) = (M.op y (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq118152 x
       have i₂ := eq59670
       grind)
    | exact superpose eq59670 eq118152
    | (have j0 := eq118152 x
       grind)
    | exact resolve eq118152 eq59670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59670 eq118152
  have eq118256 : x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq118182
       have r₂ := eq88307
       grind)
    | exact resolve eq118182 eq88307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88307 eq118182
  have eq118283 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq71349
       have i₂ := eq118256
       grind)
    | exact superpose eq118256 eq71349
    | exact resolve eq71349 eq118256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71349 eq118256
  have eq118554 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq118283
       have r₂ := eq81911
       grind)
    | exact resolve eq118283 eq81911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81911 eq118283
  have eq118709 : (σ x) = (σ (k x x)) ∨ (σ x) = (σ (k x x)) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq2015 x x
       have i₂ := eq118554
       grind)
    | exact superpose eq118554 eq2015
    | (have j0 := eq2015 x x
       grind)
    | exact resolve eq2015 eq118554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2015
  have eq118716 : (k x x) = (τ (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq80773 x x
       have i₂ := eq118554
       grind)
    | exact superpose eq118554 eq80773
    | (have j0 := eq80773 x (τ (σ x))
       grind)
    | exact resolve eq80773 eq118554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80773
  have eq119003 : (σ x) = (σ (k x x)) := by grind
  clear eq118709
  have eq119219 : x = (k x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq118716
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq118716
    | exact resolve eq118716 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118716
  have eq119220 : x = (k x x) := by grind
  clear eq119219
  have eq119228 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq119003
       have i₂ := eq81838
       grind)
    | exact superpose eq81838 eq119003
    | exact resolve eq119003 eq81838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119003
  have eq119533 : x = y := by
    first
    | (have i₁ := eq81838
       have i₂ := eq119220
       grind)
    | exact superpose eq119220 eq81838
    | exact resolve eq81838 eq119220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81838 eq119220
  have eq119796 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq119533
       grind)
    | exact superpose eq119533 eq14
    | exact resolve eq14 eq119533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119533
  have eq120107 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq119796
       have i₂ := eq65319
       grind)
    | exact superpose eq65319 eq119796
    | exact resolve eq119796 eq65319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65319 eq119796
  have eq120166 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq120107
       have i₂ := eq118554
       grind)
    | exact superpose eq118554 eq120107
    | exact resolve eq120107 eq118554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118554 eq120107
  have eq120190 : False := by grind
  exact eq120190
