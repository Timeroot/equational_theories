import equational_theories.Definability.AutBox3
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if X = Y then m(X,Y) else if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_x_y_pxx_x_pyy_y_pxy_pyx_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, a = b ∨ M.op a a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq20 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq25 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq20
    | (have j0 := eq20 (σ X0) X1
       grind)
    | exact resolve eq20 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq35 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       have j1 := eq20 X0 X1
       grind)
    | (have r₁ := eq34 X0 X1
       have r₂ := eq20 X0 X1
       grind)
    | (have r₁ := eq34 (k X0 X0) X0
       have r₂ := eq20 X0 X1
       grind)
    | (have r₁ := eq34 X0 (k X0 X0)
       have r₂ := eq20 X0 X1
       grind)
    | exact resolve eq34 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq36 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  clear eq35
  have eq45 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X1 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq36
    | (have j0 := eq36 (σ X0) X1
       grind)
    | exact resolve eq36 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq59 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X0) = X0 ∨ X0 = X1 ∨ (k X1 X1) = X1 := by
    intro X0 X1
    grind
  clear eq58
  have eq72 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq59 (σ x) (σ y)
       grind)
    | exact superpose eq59 eq16
    | (have j1 := eq59 (σ x) (σ y)
       grind)
    | (have r₁ := eq16
       have r₂ := eq59 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq59 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq72
    | exact resolve eq72 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq74 : (σ x) = (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq73
    | exact resolve eq73 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq75 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq74
    | exact resolve eq74 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq76 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ x = y ∨ y = (k y y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq59 x y
       grind)
    | exact superpose eq59 eq75
    | (have j1 := eq59 x y
       grind)
    | (have r₁ := eq75
       have r₂ := eq59 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq75
       have r₂ := eq59 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq75 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq75
  have eq77 : x = y ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ (σ x) = (σ (k x x)) ∨ y = (k y y) := by grind
  clear eq76
  have eq194 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ (σ x) = (σ (k x x)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq16
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq195 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ (σ x) = (σ (k x x)) ∨ y = (k y y) := by grind
  clear eq194
  have eq196 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ (σ x) = (σ (k x x)) ∨ y = (k y y) := by grind
  clear eq195
  have eq197 : x = (k x x) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k x x)) ∨ y = (k y y) := by
    first
    | (have r₁ := eq196
       have r₂ := eq15 x x
       grind)
    | exact resolve eq196 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq608 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = X0 ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k x x)) ∨ y = (k y y) := by
    intro X0
    first
    | (have i₁ := eq45 x X0
       have i₂ := eq197
       grind)
    | exact superpose eq197 eq45
    | (have j0 := eq45 x X0
       grind)
    | (have r₁ := eq45 y x
       have r₂ := eq197
       grind)
    | (have r₁ := eq45 x x
       have r₂ := eq197
       grind)
    | exact resolve eq45 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq610 : ∀ X0 : G, x ≠ x ∨ x = X0 ∨ (k X0 x) = (M.op x X0) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k x x)) ∨ y = (k y y) := by
    intro X0
    first
    | (have i₁ := eq36 X0 x
       have i₂ := eq197
       grind)
    | exact superpose eq197 eq36
    | (have j0 := eq36 x X0
       grind)
    | (have r₁ := eq36 X0 x
       have r₂ := eq197
       grind)
    | (have r₁ := eq36 X0 y
       have r₂ := eq197
       grind)
    | exact resolve eq36 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq613 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x = X0 ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k x x)) ∨ y = (k y y) := by
    intro X0
    first
    | (have j0 := eq610 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq615 : ∀ X0 : G, (σ x) = X0 ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k x x)) ∨ y = (k y y) := by
    intro X0
    first
    | (have j0 := eq608 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq619 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = X0 ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) := by
    intro X0
    first
    | (have j0 := eq615 X0
       have j1 := eq45 x X0
       grind)
    | (have r₁ := eq615 (σ (k x x))
       have r₂ := eq45 x x
       grind)
    | (have r₁ := eq615 X0
       have r₂ := eq45 y x
       grind)
    | (have r₁ := eq615 X0
       have r₂ := eq45 x x
       grind)
    | exact resolve eq615 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq615
  have eq5931 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq619 (σ y)
       grind)
    | exact superpose eq619 eq16
    | (have j1 := eq619 (σ y)
       grind)
    | exact resolve eq16 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq5934 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) := by grind
  clear eq5931
  have eq5937 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq5934
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq5934
    | exact resolve eq5934 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5934
  have eq5947 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k x x)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq5937
       have i₂ := eq613 y
       grind)
    | exact superpose eq613 eq5937
    | (have j1 := eq613 y
       grind)
    | exact resolve eq5937 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq5952 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) ∨ x = y ∨ (σ x) = (σ (k x x)) := by grind
  clear eq5947
  have eq5953 : x = y ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by grind
  clear eq5952
  have eq5955 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5953
       grind)
    | exact superpose eq5953 eq16
    | exact resolve eq16 eq5953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5953
  have eq5956 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by grind
  clear eq5955
  have eq5957 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by grind
  clear eq5956
  have eq5958 : y = (k y y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have r₁ := eq5957
       have r₂ := eq15 x x
       grind)
    | exact resolve eq5957 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5957
  have eq5967 : ∀ X0 : G, y ≠ y ∨ y = X0 ∨ (k y X0) = (M.op X0 y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    intro X0
    first
    | (have i₁ := eq20 y X0
       have i₂ := eq5958
       grind)
    | exact superpose eq5958 eq20
    | (have j0 := eq20 y X0
       grind)
    | (have r₁ := eq20 y x
       have r₂ := eq5958
       grind)
    | exact resolve eq20 eq5958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5968 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    intro X0
    first
    | (have i₁ := eq25 y X0
       have i₂ := eq5958
       grind)
    | exact superpose eq5958 eq25
    | (have j0 := eq25 y X0
       grind)
    | (have r₁ := eq25 y x
       have r₂ := eq5958
       grind)
    | (have r₁ := eq25 x x
       have r₂ := eq5958
       grind)
    | exact resolve eq25 eq5958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5958
  have eq5989 : ∀ X0 : G, (σ y) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    intro X0
    first
    | (have j0 := eq5968 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5968
  have eq5990 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ y = X0 ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    intro X0
    first
    | (have j0 := eq5967 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5967
  have eq5992 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = X0 ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    intro X0
    first
    | (have j0 := eq5989 X0
       have j1 := eq25 y X0
       grind)
    | (have r₁ := eq5989 (σ (k y y))
       have r₂ := eq25 y x
       grind)
    | (have r₁ := eq5989 X0
       have r₂ := eq25 y x
       grind)
    | (have r₁ := eq5989 X0
       have r₂ := eq25 x x
       grind)
    | exact resolve eq5989 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5989
  have eq6000 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5992 (σ x)
       grind)
    | exact superpose eq5992 eq16
    | (have j1 := eq5992 (σ x)
       grind)
    | exact resolve eq16 eq5992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5992
  have eq6003 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by grind
  clear eq6000
  have eq6006 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq6003
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq6003
    | exact resolve eq6003 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6003
  have eq6106 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) ∨ x = y ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq6006
       have i₂ := eq5990 x
       grind)
    | exact superpose eq5990 eq6006
    | (have j1 := eq5990 x
       grind)
    | exact resolve eq6006 eq5990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5990 eq6006
  have eq6112 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) ∨ x = y ∨ (σ y) = (σ (k y y)) := by grind
  clear eq6106
  have eq6113 : x = y ∨ (σ x) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq6112
  have eq6376 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6113
       grind)
    | exact superpose eq6113 eq16
    | exact resolve eq16 eq6113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6113
  have eq6377 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq6376
  have eq6378 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq6377
  have eq6379 : (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have r₁ := eq6378
       have r₂ := eq15 x x
       grind)
    | exact resolve eq6378 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6378
  have eq6382 : y = (τ (σ x)) ∨ (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq6379
       grind)
    | exact superpose eq6379 eq9
    | exact resolve eq9 eq6379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6379
  have eq6477 : x = y ∨ (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq6382
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq6382
    | exact resolve eq6382 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6382
  have eq6750 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6477
       grind)
    | exact superpose eq6477 eq16
    | exact resolve eq16 eq6477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6477
  have eq6751 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq6750
  have eq6752 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq6751
  have eq6753 : (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have r₁ := eq6752
       have r₂ := eq15 x x
       grind)
    | exact resolve eq6752 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6752
  have eq6763 : (k x x) = (τ (σ x)) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq6753
       grind)
    | exact superpose eq6753 eq9
    | exact resolve eq9 eq6753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6753
  have eq6872 : x = (k x x) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq6763
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq6763
    | exact resolve eq6763 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6763
  have eq7144 : ∀ X0 : G, x ≠ x ∨ x = X0 ∨ (k X0 x) = (M.op x X0) ∨ (σ y) = (σ (k y y)) := by
    intro X0
    first
    | (have i₁ := eq36 X0 x
       have i₂ := eq6872
       grind)
    | exact superpose eq6872 eq36
    | (have j0 := eq36 x X0
       grind)
    | (have r₁ := eq36 X0 x
       have r₂ := eq6872
       grind)
    | exact resolve eq36 eq6872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq6872
  have eq7167 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x = X0 ∨ (σ y) = (σ (k y y)) := by
    intro X0
    first
    | (have j0 := eq7144 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7144
  have eq7173 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) ∨ x = y ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq5937
       have i₂ := eq7167 y
       grind)
    | exact superpose eq7167 eq5937
    | (have j1 := eq7167 y
       grind)
    | exact resolve eq5937 eq7167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5937
  have eq7178 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) ∨ x = y := by grind
  clear eq7173
  have eq7179 : x = y ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) ∨ (σ x) = (σ y) := by grind
  clear eq7178
  have eq12909 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7179
       grind)
    | exact superpose eq7179 eq16
    | exact resolve eq16 eq7179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7179
  have eq12922 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) ∨ (σ x) = (σ y) := by grind
  clear eq12909
  have eq12923 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) ∨ (σ x) = (σ y) := by grind
  clear eq12922
  have eq12924 : y = (k y y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq12923
       have r₂ := eq15 x x
       grind)
    | exact resolve eq12923 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12923
  have eq12926 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq25 y X0
       have i₂ := eq12924
       grind)
    | exact superpose eq12924 eq25
    | (have j0 := eq25 y X0
       grind)
    | (have r₁ := eq25 y x
       have r₂ := eq12924
       grind)
    | exact resolve eq25 eq12924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12924
  have eq12951 : ∀ X0 : G, (σ y) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq12926 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12926
  have eq12954 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = X0 ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq12951 X0
       have j1 := eq25 y X0
       grind)
    | (have r₁ := eq12951 (σ (k y y))
       have r₂ := eq25 y x
       grind)
    | (have r₁ := eq12951 X0
       have r₂ := eq25 y x
       grind)
    | exact resolve eq12951 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq12951
  have eq12963 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12954 (σ x)
       grind)
    | exact superpose eq12954 eq16
    | (have j1 := eq12954 (σ x)
       grind)
    | exact resolve eq16 eq12954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12954
  have eq12964 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq12963
  have eq12967 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12964
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq12964
    | exact resolve eq12964 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12964
  have eq12970 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq12967
       have i₂ := eq7167 y
       grind)
    | exact superpose eq7167 eq12967
    | (have j1 := eq7167 y
       grind)
    | exact resolve eq12967 eq7167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7167
  have eq12980 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq12970
  have eq12981 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12980
       grind)
    | exact superpose eq12980 eq16
    | exact resolve eq16 eq12980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12980
  have eq12994 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq12981
  have eq12995 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq12994
  have eq12996 : (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have r₁ := eq12995
       have r₂ := eq15 x x
       grind)
    | exact resolve eq12995 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12995
  have eq12998 : y = (τ (σ x)) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq12996
       grind)
    | exact superpose eq12996 eq9
    | exact resolve eq9 eq12996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12996
  have eq13183 : x = y ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq12998
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq12998
    | exact resolve eq12998 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12998
  have eq13186 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13183
       grind)
    | exact superpose eq13183 eq16
    | exact resolve eq16 eq13183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13183
  have eq13199 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq13186
  have eq13200 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq13199
  have eq13201 : (σ y) = (σ (k y y)) := by
    first
    | (have r₁ := eq13200
       have r₂ := eq15 x x
       grind)
    | exact resolve eq13200 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13200
  have eq13217 : (k y y) = (τ (σ y)) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq13201
       grind)
    | exact superpose eq13201 eq9
    | exact resolve eq9 eq13201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13201
  have eq13414 : y = (k y y) := by
    first
    | (have i₁ := eq13217
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq13217
    | exact resolve eq13217 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13217
  have eq13422 : ∀ X0 : G, y ≠ y ∨ y = X0 ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq20 y X0
       have i₂ := eq13414
       grind)
    | exact superpose eq13414 eq20
    | (have j0 := eq20 y X0
       grind)
    | (have r₁ := eq20 y x
       have r₂ := eq13414
       grind)
    | exact resolve eq20 eq13414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq13414
  have eq13449 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq13422 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13422
  have eq13471 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12967
       have i₂ := eq13449 x
       grind)
    | exact superpose eq13449 eq12967
    | (have j1 := eq13449 x
       grind)
    | exact resolve eq12967 eq13449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12967 eq13449
  have eq13477 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq13471
  have eq13480 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13477
       grind)
    | exact superpose eq13477 eq16
    | exact resolve eq16 eq13477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13477
  have eq13497 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq13480
  have eq13498 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq13497
  have eq13499 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq13498
       have r₂ := eq15 x x
       grind)
    | exact resolve eq13498 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13498
  have eq13501 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq13499
       grind)
    | exact superpose eq13499 eq9
    | exact resolve eq9 eq13499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13499
  have eq13686 : x = y := by
    first
    | (have i₁ := eq13501
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq13501
    | exact resolve eq13501 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13501
  have eq13689 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13686
       grind)
    | exact superpose eq13686 eq16
    | exact resolve eq16 eq13686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13686
  have eq13706 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) := by grind
  clear eq13689
  have eq13707 : (k (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq13706
  have eq13708 : False := by grind
  exact eq13708

/-- `x □ y = if X = Y then m(Y,X) else if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_x_y_pxx_x_pyy_y_pyx_pyx_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, a = b ∨ M.op a a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq20 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq25 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq20
    | (have j0 := eq20 (σ X0) X1
       grind)
    | exact resolve eq20 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq35 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       have j1 := eq20 X0 X1
       grind)
    | (have r₁ := eq34 X0 X1
       have r₂ := eq20 X0 X1
       grind)
    | (have r₁ := eq34 (k X0 X0) X0
       have r₂ := eq20 X0 X1
       grind)
    | (have r₁ := eq34 X0 (k X0 X0)
       have r₂ := eq20 X0 X1
       grind)
    | exact resolve eq34 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq36 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  clear eq35
  have eq45 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X1 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq36
    | (have j0 := eq36 (σ X0) X1
       grind)
    | exact resolve eq36 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq59 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X0) = X0 ∨ X0 = X1 ∨ (k X1 X1) = X1 := by
    intro X0 X1
    grind
  clear eq58
  have eq72 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq59 (σ x) (σ y)
       grind)
    | exact superpose eq59 eq16
    | (have j1 := eq59 (σ x) (σ y)
       grind)
    | (have r₁ := eq16
       have r₂ := eq59 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq59 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq72
    | exact resolve eq72 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq74 : (σ x) = (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq73
    | exact resolve eq73 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq75 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq74
    | exact resolve eq74 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq76 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ x = y ∨ y = (k y y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq59 x y
       grind)
    | exact superpose eq59 eq75
    | (have j1 := eq59 x y
       grind)
    | (have r₁ := eq75
       have r₂ := eq59 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq75
       have r₂ := eq59 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq75 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq75
  have eq77 : x = y ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ (σ x) = (σ (k x x)) ∨ y = (k y y) := by grind
  clear eq76
  have eq194 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ (σ x) = (σ (k x x)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq16
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq195 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ (σ x) = (σ (k x x)) ∨ y = (k y y) := by grind
  clear eq194
  have eq196 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ (σ x) = (σ (k x x)) ∨ y = (k y y) := by grind
  clear eq195
  have eq197 : x = (k x x) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k x x)) ∨ y = (k y y) := by
    first
    | (have r₁ := eq196
       have r₂ := eq15 x x
       grind)
    | exact resolve eq196 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq608 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = X0 ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k x x)) ∨ y = (k y y) := by
    intro X0
    first
    | (have i₁ := eq45 x X0
       have i₂ := eq197
       grind)
    | exact superpose eq197 eq45
    | (have j0 := eq45 x X0
       grind)
    | (have r₁ := eq45 y x
       have r₂ := eq197
       grind)
    | (have r₁ := eq45 x x
       have r₂ := eq197
       grind)
    | exact resolve eq45 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq610 : ∀ X0 : G, x ≠ x ∨ x = X0 ∨ (k X0 x) = (M.op x X0) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k x x)) ∨ y = (k y y) := by
    intro X0
    first
    | (have i₁ := eq36 X0 x
       have i₂ := eq197
       grind)
    | exact superpose eq197 eq36
    | (have j0 := eq36 x X0
       grind)
    | (have r₁ := eq36 X0 x
       have r₂ := eq197
       grind)
    | (have r₁ := eq36 X0 y
       have r₂ := eq197
       grind)
    | exact resolve eq36 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq613 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x = X0 ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k x x)) ∨ y = (k y y) := by
    intro X0
    first
    | (have j0 := eq610 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq615 : ∀ X0 : G, (σ x) = X0 ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k x x)) ∨ y = (k y y) := by
    intro X0
    first
    | (have j0 := eq608 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq619 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = X0 ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) := by
    intro X0
    first
    | (have j0 := eq615 X0
       have j1 := eq45 x X0
       grind)
    | (have r₁ := eq615 (σ (k x x))
       have r₂ := eq45 x x
       grind)
    | (have r₁ := eq615 X0
       have r₂ := eq45 y x
       grind)
    | (have r₁ := eq615 X0
       have r₂ := eq45 x x
       grind)
    | exact resolve eq615 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq615
  have eq5931 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq619 (σ y)
       grind)
    | exact superpose eq619 eq16
    | (have j1 := eq619 (σ y)
       grind)
    | exact resolve eq16 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq5934 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) := by grind
  clear eq5931
  have eq5937 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq5934
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq5934
    | exact resolve eq5934 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5934
  have eq5947 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k x x)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq5937
       have i₂ := eq613 y
       grind)
    | exact superpose eq613 eq5937
    | (have j1 := eq613 y
       grind)
    | exact resolve eq5937 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq5952 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) ∨ x = y ∨ (σ x) = (σ (k x x)) := by grind
  clear eq5947
  have eq5953 : x = y ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by grind
  clear eq5952
  have eq5955 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5953
       grind)
    | exact superpose eq5953 eq16
    | exact resolve eq16 eq5953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5953
  have eq5956 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by grind
  clear eq5955
  have eq5957 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by grind
  clear eq5956
  have eq5958 : y = (k y y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have r₁ := eq5957
       have r₂ := eq15 x x
       grind)
    | exact resolve eq5957 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5957
  have eq5967 : ∀ X0 : G, y ≠ y ∨ y = X0 ∨ (k y X0) = (M.op X0 y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    intro X0
    first
    | (have i₁ := eq20 y X0
       have i₂ := eq5958
       grind)
    | exact superpose eq5958 eq20
    | (have j0 := eq20 y X0
       grind)
    | (have r₁ := eq20 y x
       have r₂ := eq5958
       grind)
    | exact resolve eq20 eq5958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5968 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    intro X0
    first
    | (have i₁ := eq25 y X0
       have i₂ := eq5958
       grind)
    | exact superpose eq5958 eq25
    | (have j0 := eq25 y X0
       grind)
    | (have r₁ := eq25 y x
       have r₂ := eq5958
       grind)
    | (have r₁ := eq25 x x
       have r₂ := eq5958
       grind)
    | exact resolve eq25 eq5958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5958
  have eq5989 : ∀ X0 : G, (σ y) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    intro X0
    first
    | (have j0 := eq5968 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5968
  have eq5990 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ y = X0 ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    intro X0
    first
    | (have j0 := eq5967 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5967
  have eq5992 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = X0 ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    intro X0
    first
    | (have j0 := eq5989 X0
       have j1 := eq25 y X0
       grind)
    | (have r₁ := eq5989 (σ (k y y))
       have r₂ := eq25 y x
       grind)
    | (have r₁ := eq5989 X0
       have r₂ := eq25 y x
       grind)
    | (have r₁ := eq5989 X0
       have r₂ := eq25 x x
       grind)
    | exact resolve eq5989 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5989
  have eq6000 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5992 (σ x)
       grind)
    | exact superpose eq5992 eq16
    | (have j1 := eq5992 (σ x)
       grind)
    | exact resolve eq16 eq5992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5992
  have eq6003 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by grind
  clear eq6000
  have eq6006 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq6003
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq6003
    | exact resolve eq6003 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6003
  have eq6106 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) ∨ x = y ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq6006
       have i₂ := eq5990 x
       grind)
    | exact superpose eq5990 eq6006
    | (have j1 := eq5990 x
       grind)
    | exact resolve eq6006 eq5990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5990 eq6006
  have eq6112 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) ∨ x = y ∨ (σ y) = (σ (k y y)) := by grind
  clear eq6106
  have eq6113 : x = y ∨ (σ x) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq6112
  have eq6376 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6113
       grind)
    | exact superpose eq6113 eq16
    | exact resolve eq16 eq6113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6113
  have eq6377 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq6376
  have eq6378 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq6377
  have eq6379 : (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have r₁ := eq6378
       have r₂ := eq15 x x
       grind)
    | exact resolve eq6378 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6378
  have eq6382 : y = (τ (σ x)) ∨ (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq6379
       grind)
    | exact superpose eq6379 eq9
    | exact resolve eq9 eq6379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6379
  have eq6477 : x = y ∨ (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq6382
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq6382
    | exact resolve eq6382 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6382
  have eq6750 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6477
       grind)
    | exact superpose eq6477 eq16
    | exact resolve eq16 eq6477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6477
  have eq6751 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq6750
  have eq6752 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq6751
  have eq6753 : (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have r₁ := eq6752
       have r₂ := eq15 x x
       grind)
    | exact resolve eq6752 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6752
  have eq6763 : (k x x) = (τ (σ x)) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq6753
       grind)
    | exact superpose eq6753 eq9
    | exact resolve eq9 eq6753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6753
  have eq6872 : x = (k x x) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq6763
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq6763
    | exact resolve eq6763 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6763
  have eq7144 : ∀ X0 : G, x ≠ x ∨ x = X0 ∨ (k X0 x) = (M.op x X0) ∨ (σ y) = (σ (k y y)) := by
    intro X0
    first
    | (have i₁ := eq36 X0 x
       have i₂ := eq6872
       grind)
    | exact superpose eq6872 eq36
    | (have j0 := eq36 x X0
       grind)
    | (have r₁ := eq36 X0 x
       have r₂ := eq6872
       grind)
    | exact resolve eq36 eq6872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq6872
  have eq7167 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x = X0 ∨ (σ y) = (σ (k y y)) := by
    intro X0
    first
    | (have j0 := eq7144 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7144
  have eq7173 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) ∨ x = y ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq5937
       have i₂ := eq7167 y
       grind)
    | exact superpose eq7167 eq5937
    | (have j1 := eq7167 y
       grind)
    | exact resolve eq5937 eq7167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5937
  have eq7178 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) ∨ x = y := by grind
  clear eq7173
  have eq7179 : x = y ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) ∨ (σ x) = (σ y) := by grind
  clear eq7178
  have eq12909 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7179
       grind)
    | exact superpose eq7179 eq16
    | exact resolve eq16 eq7179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7179
  have eq12922 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) ∨ (σ x) = (σ y) := by grind
  clear eq12909
  have eq12923 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) ∨ (σ x) = (σ y) := by grind
  clear eq12922
  have eq12924 : y = (k y y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq12923
       have r₂ := eq15 x x
       grind)
    | exact resolve eq12923 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12923
  have eq12926 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq25 y X0
       have i₂ := eq12924
       grind)
    | exact superpose eq12924 eq25
    | (have j0 := eq25 y X0
       grind)
    | (have r₁ := eq25 y x
       have r₂ := eq12924
       grind)
    | exact resolve eq25 eq12924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12924
  have eq12951 : ∀ X0 : G, (σ y) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq12926 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12926
  have eq12954 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = X0 ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq12951 X0
       have j1 := eq25 y X0
       grind)
    | (have r₁ := eq12951 (σ (k y y))
       have r₂ := eq25 y x
       grind)
    | (have r₁ := eq12951 X0
       have r₂ := eq25 y x
       grind)
    | exact resolve eq12951 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq12951
  have eq12963 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12954 (σ x)
       grind)
    | exact superpose eq12954 eq16
    | (have j1 := eq12954 (σ x)
       grind)
    | exact resolve eq16 eq12954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12954
  have eq12964 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq12963
  have eq12967 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12964
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq12964
    | exact resolve eq12964 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12964
  have eq12970 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq12967
       have i₂ := eq7167 y
       grind)
    | exact superpose eq7167 eq12967
    | (have j1 := eq7167 y
       grind)
    | exact resolve eq12967 eq7167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7167
  have eq12980 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq12970
  have eq12981 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12980
       grind)
    | exact superpose eq12980 eq16
    | exact resolve eq16 eq12980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12980
  have eq12994 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq12981
  have eq12995 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq12994
  have eq12996 : (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have r₁ := eq12995
       have r₂ := eq15 x x
       grind)
    | exact resolve eq12995 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12995
  have eq12998 : y = (τ (σ x)) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq12996
       grind)
    | exact superpose eq12996 eq9
    | exact resolve eq9 eq12996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12996
  have eq13183 : x = y ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq12998
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq12998
    | exact resolve eq12998 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12998
  have eq13186 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13183
       grind)
    | exact superpose eq13183 eq16
    | exact resolve eq16 eq13183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13183
  have eq13199 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq13186
  have eq13200 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq13199
  have eq13201 : (σ y) = (σ (k y y)) := by
    first
    | (have r₁ := eq13200
       have r₂ := eq15 x x
       grind)
    | exact resolve eq13200 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13200
  have eq13217 : (k y y) = (τ (σ y)) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq13201
       grind)
    | exact superpose eq13201 eq9
    | exact resolve eq9 eq13201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13201
  have eq13414 : y = (k y y) := by
    first
    | (have i₁ := eq13217
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq13217
    | exact resolve eq13217 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13217
  have eq13422 : ∀ X0 : G, y ≠ y ∨ y = X0 ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq20 y X0
       have i₂ := eq13414
       grind)
    | exact superpose eq13414 eq20
    | (have j0 := eq20 y X0
       grind)
    | (have r₁ := eq20 y x
       have r₂ := eq13414
       grind)
    | exact resolve eq20 eq13414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq13414
  have eq13449 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq13422 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13422
  have eq13471 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12967
       have i₂ := eq13449 x
       grind)
    | exact superpose eq13449 eq12967
    | (have j1 := eq13449 x
       grind)
    | exact resolve eq12967 eq13449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12967 eq13449
  have eq13477 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq13471
  have eq13480 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13477
       grind)
    | exact superpose eq13477 eq16
    | exact resolve eq16 eq13477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13477
  have eq13497 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq13480
  have eq13498 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq13497
  have eq13499 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq13498
       have r₂ := eq15 x x
       grind)
    | exact resolve eq13498 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13498
  have eq13501 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq13499
       grind)
    | exact superpose eq13499 eq9
    | exact resolve eq9 eq13499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13499
  have eq13686 : x = y := by
    first
    | (have i₁ := eq13501
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq13501
    | exact resolve eq13501 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13501
  have eq13689 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13686
       grind)
    | exact superpose eq13686 eq16
    | exact resolve eq16 eq13686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13686
  have eq13706 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) := by grind
  clear eq13689
  have eq13707 : (k (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq13706
  have eq13708 : False := by grind
  exact eq13708

/-- `x □ y = if X = Y then m(Y,Y) else if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_x_y_pxx_x_pyy_y_pyy_pyx_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, a = b ∨ M.op a a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq20 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq25 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq20
    | (have j0 := eq20 (σ X0) X1
       grind)
    | exact resolve eq20 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq35 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       have j1 := eq20 X0 X1
       grind)
    | (have r₁ := eq34 X0 X1
       have r₂ := eq20 X0 X1
       grind)
    | (have r₁ := eq34 (k X0 X0) X0
       have r₂ := eq20 X0 X1
       grind)
    | (have r₁ := eq34 X0 (k X0 X0)
       have r₂ := eq20 X0 X1
       grind)
    | exact resolve eq34 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq36 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  clear eq35
  have eq45 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X1 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq36
    | (have j0 := eq36 (σ X0) X1
       grind)
    | exact resolve eq36 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ X0 = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq59 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X0) = X0 ∨ X0 = X1 ∨ (k X1 X1) = X1 := by
    intro X0 X1
    grind
  clear eq58
  have eq72 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq59 (σ x) (σ y)
       grind)
    | exact superpose eq59 eq16
    | (have j1 := eq59 (σ x) (σ y)
       grind)
    | (have r₁ := eq16
       have r₂ := eq59 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq59 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq72
    | exact resolve eq72 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq74 : (σ x) = (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq73
    | exact resolve eq73 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq75 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq74
    | exact resolve eq74 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq76 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ x = y ∨ y = (k y y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq59 x y
       grind)
    | exact superpose eq59 eq75
    | (have j1 := eq59 x y
       grind)
    | (have r₁ := eq75
       have r₂ := eq59 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq75
       have r₂ := eq59 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq75 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq75
  have eq77 : x = y ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ (σ x) = (σ (k x x)) ∨ y = (k y y) := by grind
  clear eq76
  have eq194 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ (σ x) = (σ (k x x)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq16
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq195 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ (σ x) = (σ (k x x)) ∨ y = (k y y) := by grind
  clear eq194
  have eq196 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ (σ x) = (σ (k x x)) ∨ y = (k y y) := by grind
  clear eq195
  have eq197 : x = (k x x) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k x x)) ∨ y = (k y y) := by
    first
    | (have r₁ := eq196
       have r₂ := eq15 x x
       grind)
    | exact resolve eq196 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq608 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = X0 ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k x x)) ∨ y = (k y y) := by
    intro X0
    first
    | (have i₁ := eq45 x X0
       have i₂ := eq197
       grind)
    | exact superpose eq197 eq45
    | (have j0 := eq45 x X0
       grind)
    | (have r₁ := eq45 y x
       have r₂ := eq197
       grind)
    | (have r₁ := eq45 x x
       have r₂ := eq197
       grind)
    | exact resolve eq45 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq610 : ∀ X0 : G, x ≠ x ∨ x = X0 ∨ (k X0 x) = (M.op x X0) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k x x)) ∨ y = (k y y) := by
    intro X0
    first
    | (have i₁ := eq36 X0 x
       have i₂ := eq197
       grind)
    | exact superpose eq197 eq36
    | (have j0 := eq36 x X0
       grind)
    | (have r₁ := eq36 X0 x
       have r₂ := eq197
       grind)
    | (have r₁ := eq36 X0 y
       have r₂ := eq197
       grind)
    | exact resolve eq36 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq613 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x = X0 ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k x x)) ∨ y = (k y y) := by
    intro X0
    first
    | (have j0 := eq610 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq615 : ∀ X0 : G, (σ x) = X0 ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k x x)) ∨ y = (k y y) := by
    intro X0
    first
    | (have j0 := eq608 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq619 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = X0 ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) := by
    intro X0
    first
    | (have j0 := eq615 X0
       have j1 := eq45 x X0
       grind)
    | (have r₁ := eq615 (σ (k x x))
       have r₂ := eq45 x x
       grind)
    | (have r₁ := eq615 X0
       have r₂ := eq45 y x
       grind)
    | (have r₁ := eq615 X0
       have r₂ := eq45 x x
       grind)
    | exact resolve eq615 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq615
  have eq5931 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq619 (σ y)
       grind)
    | exact superpose eq619 eq16
    | (have j1 := eq619 (σ y)
       grind)
    | exact resolve eq16 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq5934 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) := by grind
  clear eq5931
  have eq5937 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq5934
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq5934
    | exact resolve eq5934 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5934
  have eq5947 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k x x)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq5937
       have i₂ := eq613 y
       grind)
    | exact superpose eq613 eq5937
    | (have j1 := eq613 y
       grind)
    | exact resolve eq5937 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq5952 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) ∨ x = y ∨ (σ x) = (σ (k x x)) := by grind
  clear eq5947
  have eq5953 : x = y ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by grind
  clear eq5952
  have eq5955 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5953
       grind)
    | exact superpose eq5953 eq16
    | exact resolve eq16 eq5953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5953
  have eq5956 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by grind
  clear eq5955
  have eq5957 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by grind
  clear eq5956
  have eq5958 : y = (k y y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have r₁ := eq5957
       have r₂ := eq15 x x
       grind)
    | exact resolve eq5957 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5957
  have eq5967 : ∀ X0 : G, y ≠ y ∨ y = X0 ∨ (k y X0) = (M.op X0 y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    intro X0
    first
    | (have i₁ := eq20 y X0
       have i₂ := eq5958
       grind)
    | exact superpose eq5958 eq20
    | (have j0 := eq20 y X0
       grind)
    | (have r₁ := eq20 y x
       have r₂ := eq5958
       grind)
    | exact resolve eq20 eq5958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5968 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    intro X0
    first
    | (have i₁ := eq25 y X0
       have i₂ := eq5958
       grind)
    | exact superpose eq5958 eq25
    | (have j0 := eq25 y X0
       grind)
    | (have r₁ := eq25 y x
       have r₂ := eq5958
       grind)
    | (have r₁ := eq25 x x
       have r₂ := eq5958
       grind)
    | exact resolve eq25 eq5958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5958
  have eq5989 : ∀ X0 : G, (σ y) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    intro X0
    first
    | (have j0 := eq5968 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5968
  have eq5990 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ y = X0 ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    intro X0
    first
    | (have j0 := eq5967 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5967
  have eq5992 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = X0 ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    intro X0
    first
    | (have j0 := eq5989 X0
       have j1 := eq25 y X0
       grind)
    | (have r₁ := eq5989 (σ (k y y))
       have r₂ := eq25 y x
       grind)
    | (have r₁ := eq5989 X0
       have r₂ := eq25 y x
       grind)
    | (have r₁ := eq5989 X0
       have r₂ := eq25 x x
       grind)
    | exact resolve eq5989 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5989
  have eq6000 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5992 (σ x)
       grind)
    | exact superpose eq5992 eq16
    | (have j1 := eq5992 (σ x)
       grind)
    | exact resolve eq16 eq5992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5992
  have eq6003 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by grind
  clear eq6000
  have eq6006 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq6003
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq6003
    | exact resolve eq6003 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6003
  have eq6106 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) ∨ x = y ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq6006
       have i₂ := eq5990 x
       grind)
    | exact superpose eq5990 eq6006
    | (have j1 := eq5990 x
       grind)
    | exact resolve eq6006 eq5990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5990 eq6006
  have eq6112 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) ∨ x = y ∨ (σ y) = (σ (k y y)) := by grind
  clear eq6106
  have eq6113 : x = y ∨ (σ x) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq6112
  have eq6376 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6113
       grind)
    | exact superpose eq6113 eq16
    | exact resolve eq16 eq6113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6113
  have eq6377 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq6376
  have eq6378 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq6377
  have eq6379 : (σ x) = (σ y) ∨ (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have r₁ := eq6378
       have r₂ := eq15 x x
       grind)
    | exact resolve eq6378 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6378
  have eq6382 : y = (τ (σ x)) ∨ (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq6379
       grind)
    | exact superpose eq6379 eq9
    | exact resolve eq9 eq6379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6379
  have eq6477 : x = y ∨ (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq6382
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq6382
    | exact resolve eq6382 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6382
  have eq6750 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6477
       grind)
    | exact superpose eq6477 eq16
    | exact resolve eq16 eq6477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6477
  have eq6751 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq6750
  have eq6752 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq6751
  have eq6753 : (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have r₁ := eq6752
       have r₂ := eq15 x x
       grind)
    | exact resolve eq6752 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6752
  have eq6763 : (k x x) = (τ (σ x)) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq6753
       grind)
    | exact superpose eq6753 eq9
    | exact resolve eq9 eq6753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6753
  have eq6872 : x = (k x x) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq6763
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq6763
    | exact resolve eq6763 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6763
  have eq7144 : ∀ X0 : G, x ≠ x ∨ x = X0 ∨ (k X0 x) = (M.op x X0) ∨ (σ y) = (σ (k y y)) := by
    intro X0
    first
    | (have i₁ := eq36 X0 x
       have i₂ := eq6872
       grind)
    | exact superpose eq6872 eq36
    | (have j0 := eq36 x X0
       grind)
    | (have r₁ := eq36 X0 x
       have r₂ := eq6872
       grind)
    | exact resolve eq36 eq6872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq6872
  have eq7167 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x = X0 ∨ (σ y) = (σ (k y y)) := by
    intro X0
    first
    | (have j0 := eq7144 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7144
  have eq7173 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) ∨ x = y ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq5937
       have i₂ := eq7167 y
       grind)
    | exact superpose eq7167 eq5937
    | (have j1 := eq7167 y
       grind)
    | exact resolve eq5937 eq7167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5937
  have eq7178 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) ∨ x = y := by grind
  clear eq7173
  have eq7179 : x = y ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) ∨ (σ x) = (σ y) := by grind
  clear eq7178
  have eq12909 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7179
       grind)
    | exact superpose eq7179 eq16
    | exact resolve eq16 eq7179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7179
  have eq12922 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) ∨ (σ x) = (σ y) := by grind
  clear eq12909
  have eq12923 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ y) = (σ (k y y)) ∨ y = (k y y) ∨ (σ x) = (σ y) := by grind
  clear eq12922
  have eq12924 : y = (k y y) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq12923
       have r₂ := eq15 x x
       grind)
    | exact resolve eq12923 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12923
  have eq12926 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq25 y X0
       have i₂ := eq12924
       grind)
    | exact superpose eq12924 eq25
    | (have j0 := eq25 y X0
       grind)
    | (have r₁ := eq25 y x
       have r₂ := eq12924
       grind)
    | exact resolve eq25 eq12924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12924
  have eq12951 : ∀ X0 : G, (σ y) = X0 ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq12926 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12926
  have eq12954 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (σ y) = X0 ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq12951 X0
       have j1 := eq25 y X0
       grind)
    | (have r₁ := eq12951 (σ (k y y))
       have r₂ := eq25 y x
       grind)
    | (have r₁ := eq12951 X0
       have r₂ := eq25 y x
       grind)
    | exact resolve eq12951 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq12951
  have eq12963 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12954 (σ x)
       grind)
    | exact superpose eq12954 eq16
    | (have j1 := eq12954 (σ x)
       grind)
    | exact resolve eq16 eq12954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12954
  have eq12964 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq12963
  have eq12967 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12964
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq12964
    | exact resolve eq12964 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12964
  have eq12970 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq12967
       have i₂ := eq7167 y
       grind)
    | exact superpose eq7167 eq12967
    | (have j1 := eq7167 y
       grind)
    | exact resolve eq12967 eq7167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7167
  have eq12980 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq12970
  have eq12981 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12980
       grind)
    | exact superpose eq12980 eq16
    | exact resolve eq16 eq12980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12980
  have eq12994 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq12981
  have eq12995 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq12994
  have eq12996 : (σ x) = (σ y) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have r₁ := eq12995
       have r₂ := eq15 x x
       grind)
    | exact resolve eq12995 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12995
  have eq12998 : y = (τ (σ x)) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq12996
       grind)
    | exact superpose eq12996 eq9
    | exact resolve eq9 eq12996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12996
  have eq13183 : x = y ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq12998
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq12998
    | exact resolve eq12998 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12998
  have eq13186 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13183
       grind)
    | exact superpose eq13183 eq16
    | exact resolve eq16 eq13183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13183
  have eq13199 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq13186
  have eq13200 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ y) = (σ (k y y)) := by grind
  clear eq13199
  have eq13201 : (σ y) = (σ (k y y)) := by
    first
    | (have r₁ := eq13200
       have r₂ := eq15 x x
       grind)
    | exact resolve eq13200 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13200
  have eq13217 : (k y y) = (τ (σ y)) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq13201
       grind)
    | exact superpose eq13201 eq9
    | exact resolve eq9 eq13201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13201
  have eq13414 : y = (k y y) := by
    first
    | (have i₁ := eq13217
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq13217
    | exact resolve eq13217 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13217
  have eq13422 : ∀ X0 : G, y ≠ y ∨ y = X0 ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq20 y X0
       have i₂ := eq13414
       grind)
    | exact superpose eq13414 eq20
    | (have j0 := eq20 y X0
       grind)
    | (have r₁ := eq20 y x
       have r₂ := eq13414
       grind)
    | exact resolve eq20 eq13414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq13414
  have eq13449 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq13422 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13422
  have eq13471 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12967
       have i₂ := eq13449 x
       grind)
    | exact superpose eq13449 eq12967
    | (have j1 := eq13449 x
       grind)
    | exact resolve eq12967 eq13449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12967 eq13449
  have eq13477 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq13471
  have eq13480 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13477
       grind)
    | exact superpose eq13477 eq16
    | exact resolve eq16 eq13477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13477
  have eq13497 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq13480
  have eq13498 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq13497
  have eq13499 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq13498
       have r₂ := eq15 x x
       grind)
    | exact resolve eq13498 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13498
  have eq13501 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq13499
       grind)
    | exact superpose eq13499 eq9
    | exact resolve eq9 eq13499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13499
  have eq13686 : x = y := by
    first
    | (have i₁ := eq13501
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq13501
    | exact resolve eq13501 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13501
  have eq13689 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13686
       grind)
    | exact superpose eq13686 eq16
    | exact resolve eq16 eq13686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13686
  have eq13706 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) := by grind
  clear eq13689
  have eq13707 : (k (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq13706
  have eq13708 : False := by grind
  exact eq13708

/-- `x □ y = if X = Y then m(X,X) else if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then m(X,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_x_y_pxx_y_pyy_x_pxx_pxy_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, a = b ∨ M.op a a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq22 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    grind
  clear eq22
  have eq28 : ∀ X0 : G, (k (σ X0) (σ (k X0 X0))) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq23
    | exact resolve eq23 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq28 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq28
    | (have j0 := eq28 X0
       grind)
    | exact resolve eq28 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq38 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq39 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X0) = X1 ∨ X0 = X1 ∨ (k X1 X1) = X0 := by
    intro X0 X1
    grind
  clear eq38
  have eq48 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq39 (σ y) (σ x)
       grind)
    | exact superpose eq39 eq16
    | (have j1 := eq39 (σ y) (σ x)
       grind)
    | (have r₁ := eq16
       have r₂ := eq39 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq39 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq48
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq48
    | exact resolve eq48 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq50 : (σ x) = (σ (k y y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq49
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq49
    | exact resolve eq49 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq51 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq50
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq50
    | exact resolve eq50 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq64 : ∀ X1 : G, (k X1 X1) = X1 ∨ (M.op (M.op X1 X1) (M.op X1 X1)) = X1 ∨ (k (M.op X1 X1) X1) = (M.op (M.op X1 X1) X1) := by
    intro X1
    grind
  have eq65 : ∀ X1 : G, (k (M.op X1 X1) (M.op X1 X1)) = X1 ∨ (k X1 X1) = X1 ∨ (k (M.op X1 X1) X1) = (M.op (M.op X1 X1) X1) := by
    intro X1
    grind
  clear eq64
  have eq66 : ∀ X1 : G, (k (k X1 X1) (k X1 X1)) = X1 ∨ (k X1 X1) = X1 ∨ (k (M.op X1 X1) X1) = (M.op (M.op X1 X1) X1) := by
    intro X1
    grind
  clear eq65
  have eq67 : ∀ X1 : G, (k (k X1 X1) (k X1 X1)) = X1 ∨ (k (k X1 X1) X1) = (M.op (k X1 X1) X1) ∨ (k X1 X1) = X1 := by
    intro X1
    grind
  clear eq66
  have eq82 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 ∨ (k (k X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 (k x x)
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq23
    | (have j0 := eq23 X0
       have j1 := eq67 X0
       grind)
    | exact resolve eq23 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq83 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq82 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq88 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ y = (k x x) := by
    first
    | (have i₁ := eq51
       have i₂ := eq39 y x
       grind)
    | exact superpose eq39 eq51
    | (have j1 := eq39 y x
       grind)
    | (have r₁ := eq51
       have r₂ := eq39 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq51
       have r₂ := eq39 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq51 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq51
  have eq89 : x = y ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ y = (k x x) := by grind
  clear eq88
  have eq102 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq83 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq83
    | exact resolve eq83 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq102 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq102
    | (have j0 := eq102 X0
       grind)
    | exact resolve eq102 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq252 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq89
       grind)
    | exact superpose eq89 eq16
    | exact resolve eq16 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq253 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ y = (k x x) := by grind
  clear eq252
  have eq254 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ y = (k x x) := by grind
  clear eq253
  have eq255 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have r₁ := eq254
       have r₂ := eq15 x x
       grind)
    | exact resolve eq254 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq1463 : x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq23 x
       have i₂ := eq255
       grind)
    | exact superpose eq255 eq23
    | exact resolve eq23 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1464 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq29 x
       have i₂ := eq255
       grind)
    | exact superpose eq255 eq29
    | exact resolve eq29 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq1474 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq1464
  have eq8793 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1463
       grind)
    | exact superpose eq1463 eq16
    | exact resolve eq16 eq1463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1463
  have eq8794 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq8793
  have eq8795 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq8794
  have eq8796 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have r₁ := eq8795
       have r₂ := eq15 x x
       grind)
    | exact resolve eq8795 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8795
  have eq9668 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1474
       grind)
    | exact superpose eq1474 eq16
    | exact resolve eq16 eq1474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1474
  have eq24491 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq9668
       have i₂ := eq8796
       grind)
    | exact superpose eq8796 eq9668
    | exact resolve eq9668 eq8796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8796 eq9668
  have eq24494 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq24491
  have eq24495 : x = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq24494
  have eq24502 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq83 y
       have i₂ := eq24495
       grind)
    | exact superpose eq24495 eq83
    | exact resolve eq83 eq24495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24505 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq107 y
       have i₂ := eq24495
       grind)
    | exact superpose eq24495 eq107
    | exact resolve eq107 eq24495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24495
  have eq24518 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq24505
  have eq24541 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24518
       grind)
    | exact superpose eq24518 eq16
    | exact resolve eq16 eq24518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24518
  have eq24557 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq24541
       have i₂ := eq24502
       grind)
    | exact superpose eq24502 eq24541
    | exact resolve eq24541 eq24502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24502 eq24541
  have eq24562 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = y := by grind
  clear eq24557
  have eq24563 : x = y ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq24562
  have eq24566 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24563
       grind)
    | exact superpose eq24563 eq16
    | exact resolve eq16 eq24563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24563
  have eq24567 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq24566
  have eq24568 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq24567
  have eq24569 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have r₁ := eq24568
       have r₂ := eq15 x x
       grind)
    | exact resolve eq24568 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24568
  have eq24573 : y = (τ (σ x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq24569
       grind)
    | exact superpose eq24569 eq9
    | exact resolve eq9 eq24569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24569
  have eq24834 : x = y ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq24573
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq24573
    | exact resolve eq24573 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24573
  have eq24847 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24834
       grind)
    | exact superpose eq24834 eq16
    | exact resolve eq16 eq24834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24834
  have eq24848 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq24847
  have eq24849 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq24848
  have eq24850 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have r₁ := eq24849
       have r₂ := eq15 x x
       grind)
    | exact resolve eq24849 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24849
  have eq24864 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq24850
       grind)
    | exact superpose eq24850 eq9
    | exact resolve eq9 eq24850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24850
  have eq25122 : y = (k x x) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq24864
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq24864
    | exact resolve eq24864 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24864
  have eq25133 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq23 x
       have i₂ := eq25122
       grind)
    | exact superpose eq25122 eq23
    | exact resolve eq23 eq25122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq25134 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq29 x
       have i₂ := eq25122
       grind)
    | exact superpose eq25122 eq29
    | exact resolve eq29 eq25122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq25122
  have eq30708 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25134
       grind)
    | exact superpose eq25134 eq16
    | exact resolve eq16 eq25134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25134
  have eq30724 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ x = y ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq30708
       have i₂ := eq25133
       grind)
    | exact superpose eq25133 eq30708
    | exact resolve eq30708 eq25133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25133 eq30708
  have eq30738 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ x = y := by grind
  clear eq30724
  have eq30739 : x = y ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq30738
  have eq30746 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30739
       grind)
    | exact superpose eq30739 eq16
    | exact resolve eq16 eq30739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30739
  have eq30760 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq30746
  have eq30761 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq30760
  have eq30762 : (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have r₁ := eq30761
       have r₂ := eq15 x x
       grind)
    | exact resolve eq30761 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30761
  have eq30766 : y = (τ (σ x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq30762
       grind)
    | exact superpose eq30762 eq9
    | exact resolve eq9 eq30762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30762
  have eq31035 : x = y ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq30766
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq30766
    | exact resolve eq30766 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30766
  have eq31048 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31035
       grind)
    | exact superpose eq31035 eq16
    | exact resolve eq16 eq31035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31035
  have eq31062 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq31048
  have eq31063 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq31062
  have eq31064 : (σ x) = (σ (k y y)) := by
    first
    | (have r₁ := eq31063
       have r₂ := eq15 x x
       grind)
    | exact resolve eq31063 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31063
  have eq31084 : (k y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq31064
       grind)
    | exact superpose eq31064 eq9
    | exact resolve eq9 eq31064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31064
  have eq31350 : x = (k y y) := by
    first
    | (have i₁ := eq31084
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq31084
    | exact resolve eq31084 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31084
  have eq31389 : (M.op x y) = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq83 y
       have i₂ := eq31350
       grind)
    | exact superpose eq31350 eq83
    | exact resolve eq83 eq31350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq31392 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq107 y
       have i₂ := eq31350
       grind)
    | exact superpose eq31350 eq107
    | exact resolve eq107 eq31350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq31350
  have eq31458 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31392
       grind)
    | exact superpose eq31392 eq16
    | exact resolve eq16 eq31392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31392
  have eq31476 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq31458
       have i₂ := eq31389
       grind)
    | exact superpose eq31389 eq31458
    | exact resolve eq31458 eq31389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31389 eq31458
  have eq31478 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq31476
  have eq31491 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31478
       grind)
    | exact superpose eq31478 eq16
    | exact resolve eq16 eq31478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31478
  have eq31507 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq31491
  have eq31508 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq31507
  have eq31509 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq31508
       have r₂ := eq15 x x
       grind)
    | exact resolve eq31508 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31508
  have eq31512 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq31509
       grind)
    | exact superpose eq31509 eq9
    | exact resolve eq9 eq31509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31509
  have eq31786 : x = y := by
    first
    | (have i₁ := eq31512
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq31512
    | exact resolve eq31512 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31512
  have eq31858 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31786
       grind)
    | exact superpose eq31786 eq16
    | exact resolve eq16 eq31786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31786
  have eq31874 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) := by grind
  clear eq31858
  have eq31875 : (k (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq31874
  have eq31876 : False := by grind
  exact eq31876

/-- `x □ y = if X = Y then m(X,X) else if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_x_y_pxx_y_pyy_x_pxx_pyx_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, a = b ∨ M.op a a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq22 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    grind
  clear eq22
  have eq28 : ∀ X0 : G, (k (σ X0) (σ (k X0 X0))) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq23
    | exact resolve eq23 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq28 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq28
    | (have j0 := eq28 X0
       grind)
    | exact resolve eq28 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq38 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq39 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X0) = X1 ∨ X0 = X1 ∨ (k X1 X1) = X0 := by
    intro X0 X1
    grind
  clear eq38
  have eq48 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq39 (σ x) (σ y)
       grind)
    | exact superpose eq39 eq16
    | (have j1 := eq39 (σ x) (σ y)
       grind)
    | (have r₁ := eq16
       have r₂ := eq39 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq39 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq48
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq48
    | exact resolve eq48 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq50 : (σ y) = (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq49
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq49
    | exact resolve eq49 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq51 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq50
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq50
    | exact resolve eq50 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq64 : ∀ X1 : G, (k X1 X1) = X1 ∨ (M.op (M.op X1 X1) (M.op X1 X1)) = X1 ∨ (k (M.op X1 X1) X1) = (M.op X1 (M.op X1 X1)) := by
    intro X1
    grind
  have eq65 : ∀ X1 : G, (k (M.op X1 X1) (M.op X1 X1)) = X1 ∨ (k X1 X1) = X1 ∨ (k (M.op X1 X1) X1) = (M.op X1 (M.op X1 X1)) := by
    intro X1
    grind
  clear eq64
  have eq66 : ∀ X1 : G, (k (k X1 X1) (k X1 X1)) = X1 ∨ (k X1 X1) = X1 ∨ (k (M.op X1 X1) X1) = (M.op X1 (M.op X1 X1)) := by
    intro X1
    grind
  clear eq65
  have eq67 : ∀ X1 : G, (k (k X1 X1) (k X1 X1)) = X1 ∨ (k (k X1 X1) X1) = (M.op X1 (k X1 X1)) ∨ (k X1 X1) = X1 := by
    intro X1
    grind
  clear eq66
  have eq82 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (k X0 X0) = X0 ∨ (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 (k x x)
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq23
    | (have j0 := eq23 X0
       have j1 := eq67 X0
       grind)
    | exact resolve eq23 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq83 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq82 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq88 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y ∨ x = (k y y) := by
    first
    | (have i₁ := eq51
       have i₂ := eq39 x y
       grind)
    | exact superpose eq39 eq51
    | (have j1 := eq39 x y
       grind)
    | (have r₁ := eq51
       have r₂ := eq39 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq51
       have r₂ := eq39 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq51 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq51
  have eq89 : x = y ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by grind
  clear eq88
  have eq102 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq83 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq83
    | exact resolve eq83 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq102 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq102
    | (have j0 := eq102 X0
       grind)
    | exact resolve eq102 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq252 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq89
       grind)
    | exact superpose eq89 eq16
    | exact resolve eq16 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq253 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by grind
  clear eq252
  have eq254 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by grind
  clear eq253
  have eq255 : y = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by
    first
    | (have r₁ := eq254
       have r₂ := eq15 x x
       grind)
    | exact resolve eq254 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq1468 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq83 x
       have i₂ := eq255
       grind)
    | exact superpose eq255 eq83
    | exact resolve eq83 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1470 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq107 x
       have i₂ := eq255
       grind)
    | exact superpose eq255 eq107
    | exact resolve eq107 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq1473 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by grind
  clear eq1470
  have eq9091 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1473
       grind)
    | exact superpose eq1473 eq16
    | exact resolve eq16 eq1473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1473
  have eq24345 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq9091
       have i₂ := eq1468
       grind)
    | exact superpose eq1468 eq9091
    | exact resolve eq9091 eq1468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1468 eq9091
  have eq24348 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) ∨ x = y := by grind
  clear eq24345
  have eq24349 : x = y ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) ∨ (σ x) = (σ y) := by grind
  clear eq24348
  have eq24350 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24349
       grind)
    | exact superpose eq24349 eq16
    | exact resolve eq16 eq24349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24349
  have eq24351 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) ∨ (σ x) = (σ y) := by grind
  clear eq24350
  have eq24352 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) ∨ (σ x) = (σ y) := by grind
  clear eq24351
  have eq24353 : x = (k y y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq24352
       have r₂ := eq15 x x
       grind)
    | exact resolve eq24352 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24352
  have eq24477 : (M.op x y) = (k y x) ∨ x = y ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq23 y
       have i₂ := eq24353
       grind)
    | exact superpose eq24353 eq23
    | exact resolve eq23 eq24353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24478 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq29 y
       have i₂ := eq24353
       grind)
    | exact superpose eq24353 eq29
    | exact resolve eq29 eq24353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24353
  have eq24499 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq24478
  have eq24811 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24499
       grind)
    | exact superpose eq24499 eq16
    | exact resolve eq16 eq24499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24499
  have eq24819 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ x = y ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq24811
       have i₂ := eq24477
       grind)
    | exact superpose eq24477 eq24811
    | exact resolve eq24811 eq24477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24477 eq24811
  have eq24824 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ x = y := by grind
  clear eq24819
  have eq24825 : x = y ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq24824
  have eq24828 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24825
       grind)
    | exact superpose eq24825 eq16
    | exact resolve eq16 eq24825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24825
  have eq24829 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq24828
  have eq24830 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq24829
  have eq24831 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq24830
       have r₂ := eq15 x x
       grind)
    | exact resolve eq24830 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24830
  have eq24845 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq24831
       grind)
    | exact superpose eq24831 eq9
    | exact resolve eq9 eq24831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24831
  have eq25106 : y = (k x x) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq24845
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq24845
    | exact resolve eq24845 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24845
  have eq25121 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq83 x
       have i₂ := eq25106
       grind)
    | exact superpose eq25106 eq83
    | exact resolve eq83 eq25106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq25124 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq107 x
       have i₂ := eq25106
       grind)
    | exact superpose eq25106 eq107
    | exact resolve eq107 eq25106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq25106
  have eq25137 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq25124
  have eq25163 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25137
       grind)
    | exact superpose eq25137 eq16
    | exact resolve eq16 eq25137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25137
  have eq25173 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ x = y ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq25163
       have i₂ := eq25121
       grind)
    | exact superpose eq25121 eq25163
    | exact resolve eq25163 eq25121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25121 eq25163
  have eq25181 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ x = y := by grind
  clear eq25173
  have eq25182 : x = y ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq25181
  have eq25185 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25182
       grind)
    | exact superpose eq25182 eq16
    | exact resolve eq16 eq25182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25182
  have eq25186 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq25185
  have eq25187 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq25186
  have eq25188 : (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have r₁ := eq25187
       have r₂ := eq15 x x
       grind)
    | exact resolve eq25187 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25187
  have eq25192 : y = (τ (σ x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq25188
       grind)
    | exact superpose eq25188 eq9
    | exact resolve eq9 eq25188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25188
  have eq25453 : x = y ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq25192
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq25192
    | exact resolve eq25192 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25192
  have eq25466 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25453
       grind)
    | exact superpose eq25453 eq16
    | exact resolve eq16 eq25453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25453
  have eq25467 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq25466
  have eq25468 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq25467
  have eq25469 : (σ x) = (σ (k y y)) := by
    first
    | (have r₁ := eq25468
       have r₂ := eq15 x x
       grind)
    | exact resolve eq25468 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25468
  have eq25488 : (k y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq25469
       grind)
    | exact superpose eq25469 eq9
    | exact resolve eq9 eq25469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25469
  have eq25746 : x = (k y y) := by
    first
    | (have i₁ := eq25488
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq25488
    | exact resolve eq25488 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25488
  have eq25780 : (M.op x y) = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq23 y
       have i₂ := eq25746
       grind)
    | exact superpose eq25746 eq23
    | exact resolve eq23 eq25746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq25781 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq29 y
       have i₂ := eq25746
       grind)
    | exact superpose eq25746 eq29
    | exact resolve eq29 eq25746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq25746
  have eq25834 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25781
       grind)
    | exact superpose eq25781 eq16
    | exact resolve eq16 eq25781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25781
  have eq25844 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq25834
       have i₂ := eq25780
       grind)
    | exact superpose eq25780 eq25834
    | exact resolve eq25834 eq25780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25780 eq25834
  have eq25855 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq25844
  have eq25856 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25855
       grind)
    | exact superpose eq25855 eq16
    | exact resolve eq16 eq25855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25855
  have eq25859 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq25856
  have eq25860 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq25859
  have eq25861 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq25860
       have r₂ := eq15 x x
       grind)
    | exact resolve eq25860 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25860
  have eq25863 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq25861
       grind)
    | exact superpose eq25861 eq9
    | exact resolve eq9 eq25861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25861
  have eq26129 : x = y := by
    first
    | (have i₁ := eq25863
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq25863
    | exact resolve eq25863 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25863
  have eq26200 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26129
       grind)
    | exact superpose eq26129 eq16
    | exact resolve eq16 eq26129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26129
  have eq26203 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) := by grind
  clear eq26200
  have eq26204 : (k (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq26203
  have eq26205 : False := by grind
  exact eq26205

/-- `x □ y = if X = Y then m(X,Y) else if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then m(X,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_x_y_pxx_y_pyy_x_pxy_pxy_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, a = b ∨ M.op a a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq22 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    grind
  clear eq22
  have eq28 : ∀ X0 : G, (k (σ X0) (σ (k X0 X0))) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq23
    | exact resolve eq23 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq28 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq28
    | (have j0 := eq28 X0
       grind)
    | exact resolve eq28 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq38 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq39 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X0) = X1 ∨ X0 = X1 ∨ (k X1 X1) = X0 := by
    intro X0 X1
    grind
  clear eq38
  have eq48 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq39 (σ y) (σ x)
       grind)
    | exact superpose eq39 eq16
    | (have j1 := eq39 (σ y) (σ x)
       grind)
    | (have r₁ := eq16
       have r₂ := eq39 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq39 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq48
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq48
    | exact resolve eq48 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq50 : (σ x) = (σ (k y y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq49
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq49
    | exact resolve eq49 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq51 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq50
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq50
    | exact resolve eq50 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq64 : ∀ X1 : G, (k X1 X1) = X1 ∨ (M.op (M.op X1 X1) (M.op X1 X1)) = X1 ∨ (k (M.op X1 X1) X1) = (M.op (M.op X1 X1) X1) := by
    intro X1
    grind
  have eq65 : ∀ X1 : G, (k (M.op X1 X1) (M.op X1 X1)) = X1 ∨ (k X1 X1) = X1 ∨ (k (M.op X1 X1) X1) = (M.op (M.op X1 X1) X1) := by
    intro X1
    grind
  clear eq64
  have eq66 : ∀ X1 : G, (k (k X1 X1) (k X1 X1)) = X1 ∨ (k X1 X1) = X1 ∨ (k (M.op X1 X1) X1) = (M.op (M.op X1 X1) X1) := by
    intro X1
    grind
  clear eq65
  have eq67 : ∀ X1 : G, (k (k X1 X1) (k X1 X1)) = X1 ∨ (k (k X1 X1) X1) = (M.op (k X1 X1) X1) ∨ (k X1 X1) = X1 := by
    intro X1
    grind
  clear eq66
  have eq82 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 ∨ (k (k X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 (k x x)
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq23
    | (have j0 := eq23 X0
       have j1 := eq67 X0
       grind)
    | exact resolve eq23 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq83 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq82 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq88 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ y = (k x x) := by
    first
    | (have i₁ := eq51
       have i₂ := eq39 y x
       grind)
    | exact superpose eq39 eq51
    | (have j1 := eq39 y x
       grind)
    | (have r₁ := eq51
       have r₂ := eq39 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq51
       have r₂ := eq39 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq51 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq51
  have eq89 : x = y ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ y = (k x x) := by grind
  clear eq88
  have eq102 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq83 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq83
    | exact resolve eq83 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq102 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq102
    | (have j0 := eq102 X0
       grind)
    | exact resolve eq102 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq252 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq89
       grind)
    | exact superpose eq89 eq16
    | exact resolve eq16 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq253 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ y = (k x x) := by grind
  clear eq252
  have eq254 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ y = (k x x) := by grind
  clear eq253
  have eq255 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have r₁ := eq254
       have r₂ := eq15 x x
       grind)
    | exact resolve eq254 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq1463 : x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq23 x
       have i₂ := eq255
       grind)
    | exact superpose eq255 eq23
    | exact resolve eq23 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1464 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq29 x
       have i₂ := eq255
       grind)
    | exact superpose eq255 eq29
    | exact resolve eq29 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq1474 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq1464
  have eq8793 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1463
       grind)
    | exact superpose eq1463 eq16
    | exact resolve eq16 eq1463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1463
  have eq8794 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq8793
  have eq8795 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq8794
  have eq8796 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have r₁ := eq8795
       have r₂ := eq15 x x
       grind)
    | exact resolve eq8795 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8795
  have eq9668 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1474
       grind)
    | exact superpose eq1474 eq16
    | exact resolve eq16 eq1474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1474
  have eq24491 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq9668
       have i₂ := eq8796
       grind)
    | exact superpose eq8796 eq9668
    | exact resolve eq9668 eq8796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8796 eq9668
  have eq24494 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq24491
  have eq24495 : x = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq24494
  have eq24502 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq83 y
       have i₂ := eq24495
       grind)
    | exact superpose eq24495 eq83
    | exact resolve eq83 eq24495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24505 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq107 y
       have i₂ := eq24495
       grind)
    | exact superpose eq24495 eq107
    | exact resolve eq107 eq24495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24495
  have eq24518 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq24505
  have eq24541 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24518
       grind)
    | exact superpose eq24518 eq16
    | exact resolve eq16 eq24518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24518
  have eq24557 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq24541
       have i₂ := eq24502
       grind)
    | exact superpose eq24502 eq24541
    | exact resolve eq24541 eq24502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24502 eq24541
  have eq24562 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = y := by grind
  clear eq24557
  have eq24563 : x = y ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq24562
  have eq24566 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24563
       grind)
    | exact superpose eq24563 eq16
    | exact resolve eq16 eq24563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24563
  have eq24567 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq24566
  have eq24568 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq24567
  have eq24569 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have r₁ := eq24568
       have r₂ := eq15 x x
       grind)
    | exact resolve eq24568 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24568
  have eq24573 : y = (τ (σ x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq24569
       grind)
    | exact superpose eq24569 eq9
    | exact resolve eq9 eq24569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24569
  have eq24834 : x = y ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq24573
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq24573
    | exact resolve eq24573 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24573
  have eq24847 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24834
       grind)
    | exact superpose eq24834 eq16
    | exact resolve eq16 eq24834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24834
  have eq24848 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq24847
  have eq24849 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq24848
  have eq24850 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have r₁ := eq24849
       have r₂ := eq15 x x
       grind)
    | exact resolve eq24849 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24849
  have eq24864 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq24850
       grind)
    | exact superpose eq24850 eq9
    | exact resolve eq9 eq24850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24850
  have eq25122 : y = (k x x) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq24864
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq24864
    | exact resolve eq24864 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24864
  have eq25133 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq23 x
       have i₂ := eq25122
       grind)
    | exact superpose eq25122 eq23
    | exact resolve eq23 eq25122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq25134 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq29 x
       have i₂ := eq25122
       grind)
    | exact superpose eq25122 eq29
    | exact resolve eq29 eq25122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq25122
  have eq30708 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25134
       grind)
    | exact superpose eq25134 eq16
    | exact resolve eq16 eq25134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25134
  have eq30724 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ x = y ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq30708
       have i₂ := eq25133
       grind)
    | exact superpose eq25133 eq30708
    | exact resolve eq30708 eq25133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25133 eq30708
  have eq30738 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ x = y := by grind
  clear eq30724
  have eq30739 : x = y ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq30738
  have eq30746 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30739
       grind)
    | exact superpose eq30739 eq16
    | exact resolve eq16 eq30739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30739
  have eq30760 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq30746
  have eq30761 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq30760
  have eq30762 : (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have r₁ := eq30761
       have r₂ := eq15 x x
       grind)
    | exact resolve eq30761 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30761
  have eq30766 : y = (τ (σ x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq30762
       grind)
    | exact superpose eq30762 eq9
    | exact resolve eq9 eq30762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30762
  have eq31035 : x = y ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq30766
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq30766
    | exact resolve eq30766 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30766
  have eq31048 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31035
       grind)
    | exact superpose eq31035 eq16
    | exact resolve eq16 eq31035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31035
  have eq31062 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq31048
  have eq31063 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq31062
  have eq31064 : (σ x) = (σ (k y y)) := by
    first
    | (have r₁ := eq31063
       have r₂ := eq15 x x
       grind)
    | exact resolve eq31063 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31063
  have eq31084 : (k y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq31064
       grind)
    | exact superpose eq31064 eq9
    | exact resolve eq9 eq31064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31064
  have eq31350 : x = (k y y) := by
    first
    | (have i₁ := eq31084
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq31084
    | exact resolve eq31084 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31084
  have eq31389 : (M.op x y) = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq83 y
       have i₂ := eq31350
       grind)
    | exact superpose eq31350 eq83
    | exact resolve eq83 eq31350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq31392 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq107 y
       have i₂ := eq31350
       grind)
    | exact superpose eq31350 eq107
    | exact resolve eq107 eq31350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq31350
  have eq31458 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31392
       grind)
    | exact superpose eq31392 eq16
    | exact resolve eq16 eq31392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31392
  have eq31476 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq31458
       have i₂ := eq31389
       grind)
    | exact superpose eq31389 eq31458
    | exact resolve eq31458 eq31389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31389 eq31458
  have eq31478 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq31476
  have eq31491 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31478
       grind)
    | exact superpose eq31478 eq16
    | exact resolve eq16 eq31478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31478
  have eq31507 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq31491
  have eq31508 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq31507
  have eq31509 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq31508
       have r₂ := eq15 x x
       grind)
    | exact resolve eq31508 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31508
  have eq31512 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq31509
       grind)
    | exact superpose eq31509 eq9
    | exact resolve eq9 eq31509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31509
  have eq31786 : x = y := by
    first
    | (have i₁ := eq31512
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq31512
    | exact resolve eq31512 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31512
  have eq31858 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31786
       grind)
    | exact superpose eq31786 eq16
    | exact resolve eq16 eq31786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31786
  have eq31874 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) := by grind
  clear eq31858
  have eq31875 : (k (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq31874
  have eq31876 : False := by grind
  exact eq31876

/-- `x □ y = if X = Y then m(X,Y) else if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_x_y_pxx_y_pyy_x_pxy_pyx_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, a = b ∨ M.op a a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq22 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    grind
  clear eq22
  have eq28 : ∀ X0 : G, (k (σ X0) (σ (k X0 X0))) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq23
    | exact resolve eq23 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq28 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq28
    | (have j0 := eq28 X0
       grind)
    | exact resolve eq28 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq38 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq39 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X0) = X1 ∨ X0 = X1 ∨ (k X1 X1) = X0 := by
    intro X0 X1
    grind
  clear eq38
  have eq48 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq39 (σ x) (σ y)
       grind)
    | exact superpose eq39 eq16
    | (have j1 := eq39 (σ x) (σ y)
       grind)
    | (have r₁ := eq16
       have r₂ := eq39 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq39 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq48
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq48
    | exact resolve eq48 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq50 : (σ y) = (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq49
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq49
    | exact resolve eq49 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq51 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq50
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq50
    | exact resolve eq50 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq64 : ∀ X1 : G, (k X1 X1) = X1 ∨ (M.op (M.op X1 X1) (M.op X1 X1)) = X1 ∨ (k (M.op X1 X1) X1) = (M.op X1 (M.op X1 X1)) := by
    intro X1
    grind
  have eq65 : ∀ X1 : G, (k (M.op X1 X1) (M.op X1 X1)) = X1 ∨ (k X1 X1) = X1 ∨ (k (M.op X1 X1) X1) = (M.op X1 (M.op X1 X1)) := by
    intro X1
    grind
  clear eq64
  have eq66 : ∀ X1 : G, (k (k X1 X1) (k X1 X1)) = X1 ∨ (k X1 X1) = X1 ∨ (k (M.op X1 X1) X1) = (M.op X1 (M.op X1 X1)) := by
    intro X1
    grind
  clear eq65
  have eq67 : ∀ X1 : G, (k (k X1 X1) (k X1 X1)) = X1 ∨ (k (k X1 X1) X1) = (M.op X1 (k X1 X1)) ∨ (k X1 X1) = X1 := by
    intro X1
    grind
  clear eq66
  have eq82 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (k X0 X0) = X0 ∨ (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 (k x x)
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq23
    | (have j0 := eq23 X0
       have j1 := eq67 X0
       grind)
    | exact resolve eq23 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq83 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq82 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq88 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y ∨ x = (k y y) := by
    first
    | (have i₁ := eq51
       have i₂ := eq39 x y
       grind)
    | exact superpose eq39 eq51
    | (have j1 := eq39 x y
       grind)
    | (have r₁ := eq51
       have r₂ := eq39 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq51
       have r₂ := eq39 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq51 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq51
  have eq89 : x = y ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by grind
  clear eq88
  have eq102 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq83 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq83
    | exact resolve eq83 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq102 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq102
    | (have j0 := eq102 X0
       grind)
    | exact resolve eq102 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq252 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq89
       grind)
    | exact superpose eq89 eq16
    | exact resolve eq16 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq253 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by grind
  clear eq252
  have eq254 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by grind
  clear eq253
  have eq255 : y = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by
    first
    | (have r₁ := eq254
       have r₂ := eq15 x x
       grind)
    | exact resolve eq254 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq1468 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq83 x
       have i₂ := eq255
       grind)
    | exact superpose eq255 eq83
    | exact resolve eq83 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1470 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq107 x
       have i₂ := eq255
       grind)
    | exact superpose eq255 eq107
    | exact resolve eq107 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq1473 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by grind
  clear eq1470
  have eq9091 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1473
       grind)
    | exact superpose eq1473 eq16
    | exact resolve eq16 eq1473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1473
  have eq24345 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq9091
       have i₂ := eq1468
       grind)
    | exact superpose eq1468 eq9091
    | exact resolve eq9091 eq1468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1468 eq9091
  have eq24348 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) ∨ x = y := by grind
  clear eq24345
  have eq24349 : x = y ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) ∨ (σ x) = (σ y) := by grind
  clear eq24348
  have eq24350 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24349
       grind)
    | exact superpose eq24349 eq16
    | exact resolve eq16 eq24349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24349
  have eq24351 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) ∨ (σ x) = (σ y) := by grind
  clear eq24350
  have eq24352 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = (k y y) ∨ (σ x) = (σ y) := by grind
  clear eq24351
  have eq24353 : x = (k y y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq24352
       have r₂ := eq15 x x
       grind)
    | exact resolve eq24352 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24352
  have eq24477 : (M.op x y) = (k y x) ∨ x = y ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq23 y
       have i₂ := eq24353
       grind)
    | exact superpose eq24353 eq23
    | exact resolve eq23 eq24353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24478 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq29 y
       have i₂ := eq24353
       grind)
    | exact superpose eq24353 eq29
    | exact resolve eq29 eq24353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24353
  have eq24499 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq24478
  have eq24811 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24499
       grind)
    | exact superpose eq24499 eq16
    | exact resolve eq16 eq24499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24499
  have eq24819 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ x = y ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq24811
       have i₂ := eq24477
       grind)
    | exact superpose eq24477 eq24811
    | exact resolve eq24811 eq24477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24477 eq24811
  have eq24824 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ x = y := by grind
  clear eq24819
  have eq24825 : x = y ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq24824
  have eq24828 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24825
       grind)
    | exact superpose eq24825 eq16
    | exact resolve eq16 eq24825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24825
  have eq24829 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq24828
  have eq24830 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq24829
  have eq24831 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq24830
       have r₂ := eq15 x x
       grind)
    | exact resolve eq24830 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24830
  have eq24845 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq24831
       grind)
    | exact superpose eq24831 eq9
    | exact resolve eq9 eq24831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24831
  have eq25106 : y = (k x x) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq24845
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq24845
    | exact resolve eq24845 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24845
  have eq25121 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq83 x
       have i₂ := eq25106
       grind)
    | exact superpose eq25106 eq83
    | exact resolve eq83 eq25106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq25124 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq107 x
       have i₂ := eq25106
       grind)
    | exact superpose eq25106 eq107
    | exact resolve eq107 eq25106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq25106
  have eq25137 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq25124
  have eq25163 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25137
       grind)
    | exact superpose eq25137 eq16
    | exact resolve eq16 eq25137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25137
  have eq25173 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ x = y ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq25163
       have i₂ := eq25121
       grind)
    | exact superpose eq25121 eq25163
    | exact resolve eq25163 eq25121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25121 eq25163
  have eq25181 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ x = y := by grind
  clear eq25173
  have eq25182 : x = y ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq25181
  have eq25185 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25182
       grind)
    | exact superpose eq25182 eq16
    | exact resolve eq16 eq25182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25182
  have eq25186 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq25185
  have eq25187 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq25186
  have eq25188 : (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have r₁ := eq25187
       have r₂ := eq15 x x
       grind)
    | exact resolve eq25187 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25187
  have eq25192 : y = (τ (σ x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq25188
       grind)
    | exact superpose eq25188 eq9
    | exact resolve eq9 eq25188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25188
  have eq25453 : x = y ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq25192
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq25192
    | exact resolve eq25192 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25192
  have eq25466 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25453
       grind)
    | exact superpose eq25453 eq16
    | exact resolve eq16 eq25453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25453
  have eq25467 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq25466
  have eq25468 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq25467
  have eq25469 : (σ x) = (σ (k y y)) := by
    first
    | (have r₁ := eq25468
       have r₂ := eq15 x x
       grind)
    | exact resolve eq25468 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25468
  have eq25488 : (k y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq25469
       grind)
    | exact superpose eq25469 eq9
    | exact resolve eq9 eq25469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25469
  have eq25746 : x = (k y y) := by
    first
    | (have i₁ := eq25488
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq25488
    | exact resolve eq25488 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25488
  have eq25780 : (M.op x y) = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq23 y
       have i₂ := eq25746
       grind)
    | exact superpose eq25746 eq23
    | exact resolve eq23 eq25746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq25781 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq29 y
       have i₂ := eq25746
       grind)
    | exact superpose eq25746 eq29
    | exact resolve eq29 eq25746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq25746
  have eq25834 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25781
       grind)
    | exact superpose eq25781 eq16
    | exact resolve eq16 eq25781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25781
  have eq25844 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq25834
       have i₂ := eq25780
       grind)
    | exact superpose eq25780 eq25834
    | exact resolve eq25834 eq25780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25780 eq25834
  have eq25855 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq25844
  have eq25856 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25855
       grind)
    | exact superpose eq25855 eq16
    | exact resolve eq16 eq25855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25855
  have eq25859 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq25856
  have eq25860 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq25859
  have eq25861 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq25860
       have r₂ := eq15 x x
       grind)
    | exact resolve eq25860 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25860
  have eq25863 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq25861
       grind)
    | exact superpose eq25861 eq9
    | exact resolve eq9 eq25861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25861
  have eq26129 : x = y := by
    first
    | (have i₁ := eq25863
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq25863
    | exact resolve eq25863 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25863
  have eq26200 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26129
       grind)
    | exact superpose eq26129 eq16
    | exact resolve eq16 eq26129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26129
  have eq26203 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) := by grind
  clear eq26200
  have eq26204 : (k (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq26203
  have eq26205 : False := by grind
  exact eq26205

/-- `x □ y = if X = Y then m(Y,X) else if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then m(X,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_x_y_pxx_y_pyy_x_pyx_pxy_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, a = b ∨ M.op a a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq22 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    grind
  clear eq22
  have eq28 : ∀ X0 : G, (k (σ X0) (σ (k X0 X0))) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq23
    | exact resolve eq23 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq28 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq28
    | (have j0 := eq28 X0
       grind)
    | exact resolve eq28 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq38 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq39 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X0) = X1 ∨ X0 = X1 ∨ (k X1 X1) = X0 := by
    intro X0 X1
    grind
  clear eq38
  have eq48 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq39 (σ y) (σ x)
       grind)
    | exact superpose eq39 eq16
    | (have j1 := eq39 (σ y) (σ x)
       grind)
    | (have r₁ := eq16
       have r₂ := eq39 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq39 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq48
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq48
    | exact resolve eq48 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq50 : (σ x) = (σ (k y y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq49
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq49
    | exact resolve eq49 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq51 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq50
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq50
    | exact resolve eq50 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq64 : ∀ X1 : G, (k X1 X1) = X1 ∨ (M.op (M.op X1 X1) (M.op X1 X1)) = X1 ∨ (k (M.op X1 X1) X1) = (M.op (M.op X1 X1) X1) := by
    intro X1
    grind
  have eq65 : ∀ X1 : G, (k (M.op X1 X1) (M.op X1 X1)) = X1 ∨ (k X1 X1) = X1 ∨ (k (M.op X1 X1) X1) = (M.op (M.op X1 X1) X1) := by
    intro X1
    grind
  clear eq64
  have eq66 : ∀ X1 : G, (k (k X1 X1) (k X1 X1)) = X1 ∨ (k X1 X1) = X1 ∨ (k (M.op X1 X1) X1) = (M.op (M.op X1 X1) X1) := by
    intro X1
    grind
  clear eq65
  have eq67 : ∀ X1 : G, (k (k X1 X1) (k X1 X1)) = X1 ∨ (k (k X1 X1) X1) = (M.op (k X1 X1) X1) ∨ (k X1 X1) = X1 := by
    intro X1
    grind
  clear eq66
  have eq82 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 ∨ (k (k X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 (k x x)
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq23
    | (have j0 := eq23 X0
       have j1 := eq67 X0
       grind)
    | exact resolve eq23 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq83 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq82 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq88 : (σ (k y x)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ y = (k x x) := by
    first
    | (have i₁ := eq51
       have i₂ := eq39 y x
       grind)
    | exact superpose eq39 eq51
    | (have j1 := eq39 y x
       grind)
    | (have r₁ := eq51
       have r₂ := eq39 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq51
       have r₂ := eq39 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq51 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq51
  have eq89 : x = y ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ y = (k x x) := by grind
  clear eq88
  have eq102 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq83 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq83
    | exact resolve eq83 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq102 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq102
    | (have j0 := eq102 X0
       grind)
    | exact resolve eq102 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq252 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq89
       grind)
    | exact superpose eq89 eq16
    | exact resolve eq16 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq253 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ y = (k x x) := by grind
  clear eq252
  have eq254 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ y = (k x x) := by grind
  clear eq253
  have eq255 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have r₁ := eq254
       have r₂ := eq15 x x
       grind)
    | exact resolve eq254 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq1463 : x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq23 x
       have i₂ := eq255
       grind)
    | exact superpose eq255 eq23
    | exact resolve eq23 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1464 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq29 x
       have i₂ := eq255
       grind)
    | exact superpose eq255 eq29
    | exact resolve eq29 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq1474 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq1464
  have eq8793 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1463
       grind)
    | exact superpose eq1463 eq16
    | exact resolve eq16 eq1463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1463
  have eq8794 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq8793
  have eq8795 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq8794
  have eq8796 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have r₁ := eq8795
       have r₂ := eq15 x x
       grind)
    | exact resolve eq8795 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8795
  have eq9668 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1474
       grind)
    | exact superpose eq1474 eq16
    | exact resolve eq16 eq1474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1474
  have eq24491 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq9668
       have i₂ := eq8796
       grind)
    | exact superpose eq8796 eq9668
    | exact resolve eq9668 eq8796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8796 eq9668
  have eq24494 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq24491
  have eq24495 : x = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq24494
  have eq24502 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq83 y
       have i₂ := eq24495
       grind)
    | exact superpose eq24495 eq83
    | exact resolve eq83 eq24495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24505 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq107 y
       have i₂ := eq24495
       grind)
    | exact superpose eq24495 eq107
    | exact resolve eq107 eq24495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24495
  have eq24518 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by grind
  clear eq24505
  have eq24541 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24518
       grind)
    | exact superpose eq24518 eq16
    | exact resolve eq16 eq24518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24518
  have eq24557 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) := by
    first
    | (have i₁ := eq24541
       have i₂ := eq24502
       grind)
    | exact superpose eq24502 eq24541
    | exact resolve eq24541 eq24502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24502 eq24541
  have eq24562 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ x = y := by grind
  clear eq24557
  have eq24563 : x = y ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq24562
  have eq24566 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24563
       grind)
    | exact superpose eq24563 eq16
    | exact resolve eq16 eq24563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24563
  have eq24567 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq24566
  have eq24568 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq24567
  have eq24569 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have r₁ := eq24568
       have r₂ := eq15 x x
       grind)
    | exact resolve eq24568 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24568
  have eq24573 : y = (τ (σ x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq24569
       grind)
    | exact superpose eq24569 eq9
    | exact resolve eq9 eq24569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24569
  have eq24834 : x = y ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq24573
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq24573
    | exact resolve eq24573 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24573
  have eq24847 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24834
       grind)
    | exact superpose eq24834 eq16
    | exact resolve eq16 eq24834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24834
  have eq24848 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq24847
  have eq24849 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq24848
  have eq24850 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have r₁ := eq24849
       have r₂ := eq15 x x
       grind)
    | exact resolve eq24849 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24849
  have eq24864 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq24850
       grind)
    | exact superpose eq24850 eq9
    | exact resolve eq9 eq24850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24850
  have eq25122 : y = (k x x) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq24864
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq24864
    | exact resolve eq24864 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24864
  have eq25133 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq23 x
       have i₂ := eq25122
       grind)
    | exact superpose eq25122 eq23
    | exact resolve eq23 eq25122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq25134 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq29 x
       have i₂ := eq25122
       grind)
    | exact superpose eq25122 eq29
    | exact resolve eq29 eq25122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq25122
  have eq30708 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25134
       grind)
    | exact superpose eq25134 eq16
    | exact resolve eq16 eq25134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25134
  have eq30724 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ x = y ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq30708
       have i₂ := eq25133
       grind)
    | exact superpose eq25133 eq30708
    | exact resolve eq30708 eq25133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25133 eq30708
  have eq30738 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ x = y := by grind
  clear eq30724
  have eq30739 : x = y ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq30738
  have eq30746 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30739
       grind)
    | exact superpose eq30739 eq16
    | exact resolve eq16 eq30739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30739
  have eq30760 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq30746
  have eq30761 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
  clear eq30760
  have eq30762 : (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have r₁ := eq30761
       have r₂ := eq15 x x
       grind)
    | exact resolve eq30761 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30761
  have eq30766 : y = (τ (σ x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq30762
       grind)
    | exact superpose eq30762 eq9
    | exact resolve eq9 eq30762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30762
  have eq31035 : x = y ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq30766
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq30766
    | exact resolve eq30766 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30766
  have eq31048 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31035
       grind)
    | exact superpose eq31035 eq16
    | exact resolve eq16 eq31035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31035
  have eq31062 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq31048
  have eq31063 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq31062
  have eq31064 : (σ x) = (σ (k y y)) := by
    first
    | (have r₁ := eq31063
       have r₂ := eq15 x x
       grind)
    | exact resolve eq31063 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31063
  have eq31084 : (k y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq31064
       grind)
    | exact superpose eq31064 eq9
    | exact resolve eq9 eq31064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31064
  have eq31350 : x = (k y y) := by
    first
    | (have i₁ := eq31084
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq31084
    | exact resolve eq31084 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31084
  have eq31389 : (M.op x y) = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq83 y
       have i₂ := eq31350
       grind)
    | exact superpose eq31350 eq83
    | exact resolve eq83 eq31350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq31392 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq107 y
       have i₂ := eq31350
       grind)
    | exact superpose eq31350 eq107
    | exact resolve eq107 eq31350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq31350
  have eq31458 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31392
       grind)
    | exact superpose eq31392 eq16
    | exact resolve eq16 eq31392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31392
  have eq31476 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq31458
       have i₂ := eq31389
       grind)
    | exact superpose eq31389 eq31458
    | exact resolve eq31458 eq31389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31389 eq31458
  have eq31478 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq31476
  have eq31491 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31478
       grind)
    | exact superpose eq31478 eq16
    | exact resolve eq16 eq31478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31478
  have eq31507 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq31491
  have eq31508 : (k (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq31507
  have eq31509 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq31508
       have r₂ := eq15 x x
       grind)
    | exact resolve eq31508 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31508
  have eq31512 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq31509
       grind)
    | exact superpose eq31509 eq9
    | exact resolve eq9 eq31509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31509
  have eq31786 : x = y := by
    first
    | (have i₁ := eq31512
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq31512
    | exact resolve eq31512 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31512
  have eq31858 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31786
       grind)
    | exact superpose eq31786 eq16
    | exact resolve eq16 eq31786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31786
  have eq31874 : (k (σ x) (σ x)) ≠ (σ (M.op x x)) := by grind
  clear eq31858
  have eq31875 : (k (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq31874
  have eq31876 : False := by grind
  exact eq31876
