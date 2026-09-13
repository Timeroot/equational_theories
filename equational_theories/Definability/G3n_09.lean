import equational_theories.Definability.AutBox3
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(X,X) = Y then m(X,Y) else if X = Y then m(Y,Y) else if m(Y,Y) = X then m(X,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_y_x_y_pyy_x_pxy_pyy_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ a = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = b ∨ a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ X0 = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq20 : (M.op x y) = (M.op x y) := by grind
  have eq21 : (M.op x y) = (M.op x y) := by grind
  clear eq20
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq23 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq22
  have eq24 : (σ x) = (σ x) := by grind
  have eq25 : (σ x) = (σ x) := by grind
  clear eq24
  have eq26 : (σ y) = (σ y) := by grind
  have eq27 : (σ y) = (σ y) := by grind
  clear eq26
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq29 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq28
  have eq30 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq31 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq27
       grind)
    | exact superpose eq27 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq38 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq27
       grind)
    | exact superpose eq27 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq46 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq27
       grind)
    | exact superpose eq27 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq52 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq46
       grind)
    | exact superpose eq46 eq16
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq64 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  have eq65 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq52
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq39
    | (have j0 := eq39 x
       grind)
    | exact resolve eq39 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq27
       grind)
    | exact superpose eq27 eq39
    | (have j0 := eq39 y
       grind)
    | exact resolve eq39 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq85 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq85
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq85
    | exact resolve eq85 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq23 eq91
    | exact resolve eq91 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq93 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  have eq98 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq108 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq98
  have eq307 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq41
  have eq387 : ∀ X0 : G, (k (σ X0) (σ (k X0 X0))) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq388 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq62 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq389 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq387 X0
       have i₂ := eq10 X0 (k X0 X0)
       grind)
    | exact superpose eq10 eq387
    | (have j0 := eq387 X0
       grind)
    | exact resolve eq387 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq2918 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq388 (τ X0)
       have i₂ := eq37 X0 (τ X0)
       grind)
    | exact superpose eq37 eq388
    | (have j0 := eq388 (τ X0)
       grind)
    | exact resolve eq388 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2925 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2918 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2918
    | (have j0 := eq2918 X0
       grind)
    | exact resolve eq2918 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2918
  have eq2931 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2925 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2925
    | (have j0 := eq2925 X0
       grind)
    | exact resolve eq2925 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2925
  have eq3167 : ∀ X0 : G, (σ (k (τ X0) (k (τ X0) (τ X0)))) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq389 (τ X0)
       have i₂ := eq37 X0 (τ X0)
       grind)
    | exact superpose eq37 eq389
    | (have j0 := eq389 (τ X0)
       grind)
    | exact resolve eq389 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq3177 : ∀ X0 : G, (σ (k (τ X0) (k (τ X0) (τ X0)))) = (M.op X0 (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3167 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3167
    | (have j0 := eq3167 X0
       grind)
    | exact resolve eq3167 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3167
  have eq3192 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k X0 (σ (k (τ X0) (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3177 X0
       have i₂ := eq37 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq37 eq3177
    | (have j0 := eq3177 X0
       grind)
    | exact resolve eq3177 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3177
  have eq3205 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k X0 (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3192 X0
       have i₂ := eq37 X0 (τ X0)
       grind)
    | exact superpose eq37 eq3192
    | (have j0 := eq3192 X0
       grind)
    | exact resolve eq3192 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq3192
  have eq3212 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3205 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3205
    | (have j0 := eq3205 X0
       grind)
    | exact resolve eq3205 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3205
  have eq3219 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3212 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3212
    | (have j0 := eq3212 X0
       grind)
    | exact resolve eq3212 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3212
  have eq5725 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq307 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq307
    | exact resolve eq307 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq5823 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (σ (k (M.op X0 X0) X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq5725 X0
       have i₂ := eq10 (M.op X0 X0) X0
       grind)
    | exact superpose eq10 eq5725
    | (have j0 := eq5725 X0
       grind)
    | exact resolve eq5725 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5725
  have eq15391 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq92 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq15392 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq15391
    | exact resolve eq15391 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15391
  have eq15403 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq15392
       have r₂ := eq30
       grind)
    | exact resolve eq15392 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15392
  have eq15405 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15403 eq65
    | exact resolve eq65 eq15403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq15403
  have eq15409 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq15405
  have eq15411 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq32 eq15409
    | exact resolve eq15409 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15409
  have eq15590 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15411 eq108
    | exact resolve eq108 eq15411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq15411
  have eq15594 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq15590
  have eq15596 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq31 eq15594
    | exact resolve eq15594 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15594
  have eq15610 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  have eq15618 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq15610
  have eq15647 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq64
       have i₂ := eq15618
       grind)
    | exact superpose eq15618 eq64
    | exact resolve eq64 eq15618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15649 : (M.op x y) = (k x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq15618
  have eq15652 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq15647
  have eq15653 : (M.op x y) = (k x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq15649
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq15649
    | exact resolve eq15649 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15649
  have eq15654 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq15652
       have i₂ := eq27
       grind)
    | exact superpose eq27 eq15652
    | exact resolve eq15652 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15652
  have eq15876 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq47
       have i₂ := eq15653
       grind)
    | exact superpose eq15653 eq47
    | exact resolve eq47 eq15653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15653
  have eq15896 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq23 eq15876
    | exact resolve eq15876 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15876
  have eq15915 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15654 eq3219
    | (have j0 := eq3219 (σ x)
       grind)
    | exact resolve eq3219 eq15654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3219
  have eq15917 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq15915
    | exact resolve eq15915 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15915
  have eq70966 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15917 eq15896
    | exact resolve eq15896 eq15917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15896 eq15917
  have eq70969 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq70966
  have eq70978 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq70969
       have r₂ := eq30
       grind)
    | exact resolve eq70969 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70969
  have eq70984 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  have eq71010 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq70984 eq15654
    | exact resolve eq15654 eq70984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15654 eq70984
  have eq71029 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq71010
  have eq71046 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq71029 eq70978
    | exact resolve eq70978 eq71029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70978 eq71029
  have eq71052 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq71046
  have eq71070 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  have eq71078 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq71070
  have eq71845 : (k y y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq71078
  have eq72618 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq71052
       have i₂ := eq71845
       grind)
    | exact superpose eq71845 eq71052
    | exact resolve eq71052 eq71845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71052 eq71845
  have eq72625 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq72618
  have eq72637 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq93
       have i₂ := eq72625
       grind)
    | exact superpose eq72625 eq93
    | exact resolve eq93 eq72625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72638 : (M.op x y) = (k x y) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq72625
  have eq72640 : (M.op x y) = (k x y) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq72638
  have eq72641 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq72637
  have eq72643 : (M.op x y) = (k x y) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72640
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq72640
    | exact resolve eq72640 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72640
  have eq72644 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72641
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq72641
    | exact resolve eq72641 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72641
  have eq73267 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  have eq77023 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq47
       have i₂ := eq72643
       grind)
    | exact superpose eq72643 eq47
    | exact resolve eq47 eq72643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72643
  have eq77066 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq23 eq77023
    | exact resolve eq77023 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77023
  have eq77071 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq73267
  have eq105334 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq77071 eq72644
    | exact resolve eq72644 eq77071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72644 eq77071
  have eq105385 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq105334
  have eq106113 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq105385
  have eq106115 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq106113
  have eq106118 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq106115
    | exact resolve eq106115 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106115
  have eq106519 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq106118 eq77066
    | exact resolve eq77066 eq106118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106522 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq106519
  have eq106533 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq106522
       have r₂ := eq30
       grind)
    | exact resolve eq106522 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106522
  have eq106539 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq106533
  have eq106544 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq29 eq106539
    | exact resolve eq106539 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106539
  have eq106566 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq106544 eq77066
    | exact resolve eq77066 eq106544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77066 eq106544
  have eq106569 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq106566
  have eq106580 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq106569
       have r₂ := eq30
       grind)
    | exact resolve eq106569 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106569
  have eq106586 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq106580
  have eq106592 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq106586
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq106586
    | exact resolve eq106586 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106586
  have eq107480 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq47
       have i₂ := eq106592
       grind)
    | exact superpose eq106592 eq47
    | exact resolve eq47 eq106592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106592
  have eq107523 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq23 eq107480
    | exact resolve eq107480 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107480
  have eq108465 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq107523 eq106118
    | exact resolve eq106118 eq107523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106118
  have eq108470 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq108465
  have eq108488 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq108470
       have r₂ := eq30
       grind)
    | exact resolve eq108470 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108470
  have eq108563 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq108488
  have eq108568 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq108563
    | exact resolve eq108563 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108563
  have eq109327 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq108568 eq107523
    | exact resolve eq107523 eq108568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107523 eq108568
  have eq109330 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq109327
  have eq109343 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq109330
       have r₂ := eq30
       grind)
    | exact resolve eq109330 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109330
  have eq109347 : (k x x) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  have eq110056 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq46
       have i₂ := eq109347
       grind)
    | exact superpose eq109347 eq46
    | exact resolve eq46 eq109347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq110072 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq15596
       have i₂ := eq109347
       grind)
    | exact superpose eq109347 eq15596
    | exact resolve eq15596 eq109347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15596 eq109347
  have eq110109 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq110072
  have eq110126 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq110056
       have i₂ := eq109343
       grind)
    | exact superpose eq109343 eq110056
    | exact resolve eq110056 eq109343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110056
  have eq110249 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq110126
  have eq110255 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq110249
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq110249
    | exact resolve eq110249 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110249
  have eq110292 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq110255 eq2931
    | (have j0 := eq2931 (σ x)
       grind)
    | (have r₁ := eq2931 (σ x)
       have r₂ := eq110255
       grind)
    | exact resolve eq2931 eq110255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2931 eq110255
  have eq110299 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq110292
  have eq2149814 : x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq109343
       have i₂ := eq110109
       grind)
    | exact superpose eq110109 eq109343
    | exact resolve eq109343 eq110109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110109
  have eq2151156 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq2149814
  have eq2153809 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  have eq2153822 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2153809
  have eq2153941 : (k y y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2153822
  have eq2156735 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2151156
       have i₂ := eq2153941
       grind)
    | exact superpose eq2153941 eq2151156
    | exact resolve eq2151156 eq2153941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2151156 eq2153941
  have eq2156746 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2156735
  have eq2156801 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq93
       have i₂ := eq2156746
       grind)
    | exact superpose eq2156746 eq93
    | exact resolve eq93 eq2156746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq2156811 : (σ (M.op x y)) = (σ (k x y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5823 y
       have i₂ := eq2156746
       grind)
    | exact superpose eq2156746 eq5823
    | exact resolve eq5823 eq2156746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5823 eq2156746
  have eq2156819 : (σ (M.op x y)) = (σ (k x y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq2156811
  have eq2156829 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2156801
  have eq2156835 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2156819
       have i₂ := eq47
       grind)
    | exact superpose eq47 eq2156819
    | exact resolve eq2156819 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq2156819
  have eq2156843 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2156829
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2156829
    | exact resolve eq2156829 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2156829
  have eq2156846 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2156835
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq2156835
    | exact resolve eq2156835 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2156835
  have eq2156850 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq23 eq2156846
    | exact resolve eq2156846 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2156846
  have eq2158979 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  have eq2180747 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2158979
  have eq2351473 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq2180747 eq2156843
    | exact resolve eq2156843 eq2180747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2156843 eq2180747
  have eq2351592 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2351473
  have eq2351652 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2351592
  have eq2351654 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq2351652
  have eq2351665 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq29 eq2351654
    | exact resolve eq2351654 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2351654
  have eq2356165 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq2351665 eq2156850
    | exact resolve eq2156850 eq2351665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2156850 eq2351665
  have eq2356170 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2356165
  have eq2356187 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq2356170
       have r₂ := eq30
       grind)
    | exact resolve eq2356170 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2356170
  have eq2359549 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2356187 eq110299
    | exact resolve eq110299 eq2356187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110299 eq2356187
  have eq2360827 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2359549
  have eq2361327 : x = y ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq109343
       have i₂ := eq2360827
       grind)
    | exact superpose eq2360827 eq109343
    | exact resolve eq109343 eq2360827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109343 eq2360827
  have eq2362677 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2361327
  have eq2363267 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq2362677 eq32
    | exact resolve eq32 eq2362677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq2362677
  have eq2363760 : x = y ∨ x = y := by
    first
    | exact superpose eq31 eq2363267
    | exact resolve eq2363267 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2363267
  have eq2363761 : x = y := by grind
  clear eq2363760
  have eq2366643 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq21
       have i₂ := eq2363761
       grind)
    | exact superpose eq2363761 eq21
    | exact resolve eq21 eq2363761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq2366644 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq27
       have i₂ := eq2363761
       grind)
    | exact superpose eq2363761 eq27
    | exact resolve eq27 eq2363761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2363761
  have eq2367830 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2366644
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2366644
    | exact resolve eq2366644 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2366644
  have eq2367836 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2367830 eq29
    | exact resolve eq29 eq2367830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2367830
  have eq2368400 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq64
       have i₂ := eq2366643
       grind)
    | exact superpose eq2366643 eq64
    | exact resolve eq64 eq2366643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq2369096 : (k x (M.op x y)) = (M.op x (M.op x y)) := by grind
  have eq2369109 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23 eq2368400
    | exact resolve eq2368400 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2368400
  have eq2369781 : (k (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by grind
  have eq2379882 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  have eq2379901 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2367836 eq2379882
    | exact resolve eq2379882 eq2367836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2379882
  have eq2379953 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2379901
       have r₂ := eq30
       grind)
    | exact resolve eq2379901 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2379901
  have eq2379978 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2367836 eq2379953
    | exact resolve eq2379953 eq2367836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2379953
  have eq2380004 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2379978 eq2369781
    | exact resolve eq2369781 eq2379978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2369781 eq2379978
  have eq2380006 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2367836 eq2380004
    | exact resolve eq2380004 eq2367836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2380004
  have eq2381837 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2380006 eq2369109
    | exact resolve eq2369109 eq2380006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2369109 eq2380006
  have eq2381851 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2381837
  have eq2381858 : x = (M.op x y) := by
    first
    | (have r₁ := eq2381851
       have r₂ := eq30
       grind)
    | exact resolve eq2381851 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2381851
  have eq2381912 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2381858 eq23
    | exact resolve eq23 eq2381858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq2382792 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq2381858 eq2369096
    | exact resolve eq2369096 eq2381858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2369096
  have eq2382795 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq2382792
       have i₂ := eq2366643
       grind)
    | exact superpose eq2366643 eq2382792
    | exact resolve eq2382792 eq2366643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2366643 eq2382792
  have eq2383377 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2381912
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2381912
    | exact resolve eq2381912 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2381912
  have eq2383379 : x = (k x x) := by
    first
    | exact superpose eq2381858 eq2382795
    | exact resolve eq2382795 eq2381858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2381858 eq2382795
  have eq2386478 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq388 x
       have i₂ := eq2383379
       grind)
    | exact superpose eq2383379 eq388
    | (have j0 := eq388 x
       grind)
    | exact resolve eq388 eq2383379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388 eq2383379
  have eq2386496 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2386478
  have eq2386513 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2386496
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2386496
    | exact resolve eq2386496 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2386496
  have eq2386604 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2367836 eq2386513
    | exact resolve eq2386513 eq2367836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2367836 eq2386513
  have eq2386690 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2383377 eq2386604
    | exact resolve eq2386604 eq2383377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2383377 eq2386604
  have eq2386774 : False := by grind
  exact eq2386774

/-- `x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then m(X,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxy_pyx_pxx_y_pyy_x_pxy_pxy_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq9
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq43 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq34 (τ X0)
       grind)
    | exact superpose eq34 eq19
    | exact resolve eq19 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq31
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq31 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq75 : ∀ X1 : G, (M.op (M.op X1 X1) (M.op X1 X1)) = X1 ∨ (M.op (M.op X1 X1) X1) = (k (M.op X1 X1) X1) := by
    intro X1
    grind
  have eq78 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq34 (M.op x x)
       have i₂ := eq75 x
       grind)
    | exact superpose eq75 eq34
    | (have j1 := eq75 X0
       grind)
    | exact resolve eq34 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq79 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq78 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq88 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq24 (σ X0) X0
       have i₂ := eq25 (σ X0)
       grind)
    | exact superpose eq25 eq24
    | exact resolve eq24 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq89 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq20 X0 (τ X0)
       have i₂ := eq25 (τ X0)
       grind)
    | exact superpose eq25 eq20
    | exact resolve eq20 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq89 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq89
    | exact resolve eq89 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq91 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq88 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq88
    | exact resolve eq88 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq98 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq90 X0
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq90
    | exact resolve eq90 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq99 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq91 X0
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq91
    | exact resolve eq91 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq91
  have eq104 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq20 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq79 (τ X0)
       grind)
    | exact superpose eq79 eq20
    | exact resolve eq20 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq105 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq98 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq98
    | exact resolve eq98 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op (τ X0) (τ X0))
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq9
    | exact resolve eq9 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq335 : ∀ X0 : G, (k X0 (σ (τ (M.op X0 X0)))) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq43 X0
       have i₂ := eq112 X0
       grind)
    | exact superpose eq112 eq43
    | exact resolve eq43 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq336 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq335 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq335
    | exact resolve eq335 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq337 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq336 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq336
    | exact resolve eq336 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq336
  have eq338 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op X0 (τ (M.op (σ X0) (σ X0))))) := by
    intro X0
    first
    | (have i₁ := eq337 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq337
    | exact resolve eq337 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq368 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq338 X0
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq338
    | exact resolve eq338 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq372 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq368 X0
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq368
    | exact resolve eq368 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq393 : ∀ X0 : G, (σ (M.op (τ (M.op X0 X0)) (τ X0))) = (k (σ (τ (M.op X0 X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq104 X0
       have i₂ := eq112 X0
       grind)
    | exact superpose eq112 eq104
    | exact resolve eq104 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq112
  have eq394 : ∀ X0 : G, (k (M.op X0 X0) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq393 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq393
    | exact resolve eq393 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq395 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq394 X0
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq394
    | exact resolve eq394 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq394
  have eq400 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (τ (M.op (σ X0) (σ X0))) X0)) := by
    intro X0
    first
    | (have i₁ := eq395 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq395
    | exact resolve eq395 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq424 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq400 X0
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq400
    | exact resolve eq400 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq400
  have eq428 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq424 X0
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq424
    | exact resolve eq424 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq3973 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ (M.op X1 X1)) = X0 ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq59 X0 X1
       have i₂ := eq105 X1
       grind)
    | exact superpose eq105 eq59
    | (have j0 := eq59 X0 X1
       grind)
    | exact resolve eq59 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq4069 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (σ (M.op (τ X0) (τ X0))) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3973 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3973
    | (have j0 := eq3973 X1 (τ X0)
       grind)
    | exact resolve eq3973 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3973
  have eq4162 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (σ (M.op (τ X0) (τ X0))) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4069 X0 X1
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq4069
    | (have j0 := eq4069 X0 X1
       grind)
    | exact resolve eq4069 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq4069
  have eq4174 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4162 X0 X1
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq4162
    | (have j0 := eq4162 X0 X1
       grind)
    | exact resolve eq4162 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4162
  have eq17502 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4174 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4174
    | (have j0 := eq4174 (σ X0) (σ X1)
       grind)
    | exact resolve eq4174 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4174
  have eq17779 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17502 X0 X1
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq17502
    | (have j0 := eq17502 X0 X1
       grind)
    | exact resolve eq17502 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17502
  have eq17801 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17779 X0 X1
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq17779
    | (have j0 := eq17779 X0 X1
       grind)
    | exact resolve eq17779 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17779
  have eq17802 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17801 X0 X1
       have i₂ := eq105 X1
       grind)
    | exact superpose eq105 eq17801
    | (have j0 := eq17801 X0 X1
       grind)
    | exact resolve eq17801 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17801
  have eq1169792 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq17802 X0 X1
       grind)
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq17802 X0 X1
       grind)
    | exact superpose eq17802 eq11
    | (have j1 := eq17802 X1 X0
       grind)
    | (have r₁ := eq11 (σ X1) (σ X0)
       have r₂ := eq17802 X0 X1
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq17802 X0 X1
       grind)
    | exact resolve eq11 eq17802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17802
  have eq1169807 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1169792 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169792
  have eq1169879 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1169807 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1169807
    | (have j0 := eq1169807 X0 X1
       grind)
    | exact resolve eq1169807 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169807
  have eq1943241 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op (τ X0) (τ X0))) ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1169879 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1169879
    | (have j0 := eq1169879 X1 (τ X0)
       grind)
    | exact resolve eq1169879 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169879
  have eq1945280 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op (τ X0) (τ X0))) ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1943241 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq1943241
    | (have j0 := eq1943241 X0 X1
       grind)
    | exact resolve eq1943241 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1943241
  have eq1945791 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op (σ X1) X0)) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1945280 X0 X1
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq1945280
    | (have j0 := eq1945280 X0 X1
       grind)
    | exact resolve eq1945280 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1945280
  have eq1950880 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (σ X1) X0)
       have i₂ := eq1945791 X0 X1
       grind)
    | exact superpose eq1945791 eq10
    | (have j1 := eq1945791 X0 X1
       grind)
    | exact resolve eq10 eq1945791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1945791
  have eq1952119 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1950880 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq1950880
    | (have j0 := eq1950880 X0 X1
       grind)
    | exact resolve eq1950880 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1950880
  have eq1952120 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1952119 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1952119
  have eq1956763 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1952120 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1952120
    | (have j0 := eq1952120 X1 (τ X0)
       grind)
    | exact resolve eq1952120 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1957565 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1952120 (σ X1) X0
       grind)
    | exact superpose eq1952120 eq15
    | (have j1 := eq1952120 (σ X1) X0
       grind)
    | exact resolve eq15 eq1952120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1952120
  have eq1958869 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1957565 X0 X1
       have i₂ := eq105 X1
       grind)
    | exact superpose eq105 eq1957565
    | (have j0 := eq1957565 X0 X1
       grind)
    | exact resolve eq1957565 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq1957565
  have eq1958972 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1956763 X0 X1
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq1956763
    | (have j0 := eq1956763 X0 X1
       grind)
    | exact resolve eq1956763 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq1956763
  have eq2079451 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1958869 x y
       grind)
    | exact superpose eq1958869 eq16
    | (have j1 := eq1958869 x y
       grind)
    | exact resolve eq16 eq1958869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1958869
  have eq2081816 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2079451
       have i₂ := eq1958972 x y
       grind)
    | exact superpose eq1958972 eq2079451
    | (have j1 := eq1958972 x y
       grind)
    | exact resolve eq2079451 eq1958972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1958972 eq2079451
  have eq2081828 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq2081816
  have eq2097418 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq372 x
       have i₂ := eq2081828
       grind)
    | exact superpose eq2081828 eq372
    | exact resolve eq372 eq2081828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2081828
  have eq2097599 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq2097418
       have r₂ := eq16
       grind)
    | exact resolve eq2097418 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2097418
  have eq2101251 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq428 y
       have i₂ := eq2097599
       grind)
    | exact superpose eq2097599 eq428
    | exact resolve eq428 eq2097599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2097599
  have eq2101427 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq2101251
       have r₂ := eq16
       grind)
    | exact resolve eq2101251 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2101251
  have eq2101480 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq2101427
       grind)
    | exact superpose eq2101427 eq9
    | exact resolve eq9 eq2101427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2101427
  have eq2102211 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2101480
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2101480
    | exact resolve eq2101480 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2101480
  have eq2102219 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq372 x
       have i₂ := eq2102211
       grind)
    | exact superpose eq2102211 eq372
    | exact resolve eq372 eq2102211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372 eq2102211
  have eq2102399 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq2102219
       have r₂ := eq16
       grind)
    | exact resolve eq2102219 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2102219
  have eq2106091 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq2102399
       grind)
    | exact superpose eq2102399 eq9
    | exact resolve eq9 eq2102399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2102399
  have eq2106823 : x = (M.op y y) := by
    first
    | (have i₁ := eq2106091
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq2106091
    | exact resolve eq2106091 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2106091
  have eq2106835 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq428 y
       have i₂ := eq2106823
       grind)
    | exact superpose eq2106823 eq428
    | exact resolve eq428 eq2106823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428 eq2106823
  have eq2107011 : False := by grind
  exact eq2107011

/-- `x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxy_pyx_pxx_y_pyy_x_pxy_pyx_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq19 : (M.op x y) = (M.op x y) := by grind
  have eq20 : (M.op x y) = (M.op x y) := by grind
  clear eq19
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq21
  have eq23 : (σ x) = (σ x) := by grind
  have eq24 : (σ x) = (σ x) := by grind
  clear eq23
  have eq25 : (σ y) = (σ y) := by grind
  have eq26 : (σ y) = (σ y) := by grind
  clear eq25
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq27
  have eq29 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq51 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq52 x
       grind)
    | exact superpose eq52 eq45
    | exact resolve eq45 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq56 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq55
       have i₂ := eq52 sF2
       grind)
    | exact superpose eq52 eq55
    | exact resolve eq55 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq67 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq51
       have i₂ := eq52 sF2
       grind)
    | exact superpose eq52 eq51
    | exact resolve eq51 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq68 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq67
       have i₂ := eq52 x
       grind)
    | exact superpose eq52 eq67
    | exact resolve eq67 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq74 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq11 X1 (M.op X1 X1)
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq11 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq46
       have i₂ := eq74 x y
       grind)
    | exact superpose eq74 eq46
    | (have j1 := eq74 x y
       grind)
    | exact resolve eq46 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq82
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq82
    | exact resolve eq82 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq22 eq88
    | exact resolve eq88 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq96 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq101 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq97
       have i₂ := eq52 sF3
       grind)
    | exact superpose eq52 eq97
    | exact resolve eq97 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq103 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq101
       have i₂ := eq52 y
       grind)
    | exact superpose eq52 eq101
    | exact resolve eq101 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq118 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq119 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq118 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq120 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq119 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq126 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq103
       grind)
    | exact superpose eq103 eq16
    | exact resolve eq16 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq36 X0 (τ X0)
       have i₂ := eq52 (τ X0)
       grind)
    | exact superpose eq52 eq36
    | exact resolve eq36 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) ∨ (M.op (M.op (τ X0) (τ X0)) (τ X0)) = (M.op (τ X0) (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq36
  have eq280 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq268 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq268
    | exact resolve eq268 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq281 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq280 X0
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq280
    | exact resolve eq280 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq280
  have eq703 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq281 X0
       grind)
    | exact superpose eq281 eq16
    | exact resolve eq16 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq6238 : ∀ X0 : G, (k X0 (σ (τ (M.op X0 X0)))) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) ∨ (M.op (M.op (τ X0) (τ X0)) (τ X0)) = (M.op (τ X0) (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq270 X0
       have i₂ := eq703 X0
       grind)
    | exact superpose eq703 eq270
    | (have j0 := eq270 X0
       grind)
    | exact resolve eq270 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq6239 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) ∨ (M.op (M.op (τ X0) (τ X0)) (τ X0)) = (M.op (τ X0) (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6238 X0
       have i₂ := eq15 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq6238
    | (have j0 := eq6238 X0
       grind)
    | exact resolve eq6238 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6238
  have eq6240 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (M.op (τ (M.op X0 X0)) (τ X0)) ∨ (k X0 (M.op X0 X0)) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6239 X0
       have i₂ := eq703 X0
       grind)
    | exact superpose eq703 eq6239
    | (have j0 := eq6239 X0
       grind)
    | exact resolve eq6239 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703 eq6239
  have eq14652 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq90 eq74
    | (have j0 := eq74 (σ x) (σ y)
       grind)
    | exact resolve eq74 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq90
  have eq14653 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq28 eq14652
    | exact resolve eq14652 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14652
  have eq14664 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq14653
       have r₂ := eq29
       grind)
    | exact resolve eq14653 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14653
  have eq14668 : (τ (σ y)) = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14664 eq68
    | exact resolve eq68 eq14664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq14664
  have eq14705 : y = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq14668
    | exact resolve eq14668 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14668
  have eq14706 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq14705
  have eq14722 : (τ (σ x)) = (M.op y y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14706 eq126
    | exact resolve eq126 eq14706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14706
  have eq14752 : x = (M.op y y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq14722
    | exact resolve eq14722 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14722
  have eq14753 : y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq14752
  have eq14769 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq56
       have i₂ := eq14753
       grind)
    | exact superpose eq14753 eq56
    | exact resolve eq56 eq14753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq14782 : (M.op x y) = (k y x) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq120 x
       have i₂ := eq14753
       grind)
    | exact superpose eq14753 eq120
    | exact resolve eq120 eq14753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14753
  have eq14787 : (M.op x y) = (k y x) ∨ x = (M.op y y) := by grind
  clear eq14782
  have eq14793 : (M.op x y) = (k y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14787
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq14787
    | exact resolve eq14787 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14787
  have eq14806 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14769
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq14769
    | exact resolve eq14769 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq14769
  have eq15063 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq14793
       grind)
    | exact superpose eq14793 eq96
    | exact resolve eq96 eq14793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14793
  have eq15083 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq22 eq15063
    | exact resolve eq15063 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15063
  have eq15099 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14806 eq120
    | exact resolve eq120 eq14806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq14806
  have eq15108 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq15099
    | exact resolve eq15099 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15099
  have eq16061 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15108 eq15083
    | exact resolve eq15083 eq15108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15083 eq15108
  have eq16068 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq16061
  have eq16075 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq16068
       have r₂ := eq29
       grind)
    | exact resolve eq16068 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16068
  have eq16157 : (τ (σ x)) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16075 eq126
    | exact resolve eq126 eq16075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq16075
  have eq16186 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq16157
    | exact resolve eq16157 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16157
  have eq16187 : x = (M.op y y) := by grind
  clear eq16186
  have eq16202 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq103
       have i₂ := eq16187
       grind)
    | exact superpose eq16187 eq103
    | exact resolve eq103 eq16187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq16187
  have eq16238 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16202
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16202
    | exact resolve eq16202 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq16202
  have eq16268 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  have eq16273 : (M.op (τ (σ x)) (τ (σ y))) = (M.op (τ (σ y)) (τ (σ x))) ∨ (k (σ y) (σ x)) = (σ (M.op (τ (σ x)) (τ (σ y)))) := by
    first
    | exact superpose eq16238 eq6240
    | exact resolve eq6240 eq16238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6240 eq16238
  have eq16276 : (M.op x (τ (σ y))) = (M.op (τ (σ y)) x) ∨ (k (σ y) (σ x)) = (σ (M.op (τ (σ x)) (τ (σ y)))) := by
    first
    | exact superpose eq30 eq16273
    | exact resolve eq16273 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16273
  have eq16278 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq28 eq16268
    | exact resolve eq16268 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16268
  have eq16291 : (M.op x y) = (M.op y x) ∨ (k (σ y) (σ x)) = (σ (M.op (τ (σ x)) (τ (σ y)))) := by
    first
    | exact superpose eq31 eq16276
    | exact resolve eq16276 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16276
  have eq16293 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq28 eq16278
    | exact resolve eq16278 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16278
  have eq16296 : (M.op x y) = (M.op y x) ∨ (k (σ y) (σ x)) = (σ (M.op (τ (σ x)) (τ (σ y)))) := by
    first
    | (have i₁ := eq16291
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq16291
    | exact resolve eq16291 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16291
  have eq16300 : (k (σ y) (σ x)) = (σ (M.op (τ (σ x)) y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq31 eq16296
    | exact resolve eq16296 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq16296
  have eq16302 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq30 eq16300
    | exact resolve eq16300 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq16300
  have eq16303 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq16302
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq16302
    | exact resolve eq16302 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16302
  have eq16304 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq22 eq16303
    | exact resolve eq16303 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16303
  have eq16711 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq16304 eq16293
    | exact resolve eq16293 eq16304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16713 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq16711
       have r₂ := eq29
       grind)
    | exact resolve eq16711 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16711
  have eq16727 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq16713 eq14
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq16713
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq16713
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq16713
       grind)
    | exact resolve eq14 eq16713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16713
  have eq16728 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq16727
       have r₂ := eq28
       grind)
    | exact resolve eq16727 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16727
  have eq16836 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq16728 eq16304
    | exact resolve eq16304 eq16728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16304 eq16728
  have eq16838 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq16836
  have eq16840 : (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq16838
       have r₂ := eq29
       grind)
    | exact resolve eq16838 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16838
  have eq16843 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq16840
       grind)
    | exact superpose eq16840 eq14
    | (have r₁ := eq14 x y
       have r₂ := eq16840
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq16840
       grind)
    | exact resolve eq14 eq16840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16840
  have eq16844 : (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq16843
       have r₂ := eq20
       grind)
    | exact resolve eq16843 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq16843
  have eq16933 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq96
       have i₂ := eq16844
       grind)
    | exact superpose eq16844 eq96
    | exact resolve eq96 eq16844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq16844
  have eq16955 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq22 eq16933
    | exact resolve eq16933 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq16933
  have eq17088 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq16955 eq16293
    | exact resolve eq16293 eq16955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16293
  have eq17091 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq17088
       have r₂ := eq29
       grind)
    | exact resolve eq17088 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17088
  have eq17133 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq17091 eq14
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq17091
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq17091
       grind)
    | exact resolve eq14 eq17091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17091
  have eq17134 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq17133
       have r₂ := eq28
       grind)
    | exact resolve eq17133 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq17133
  have eq17136 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16955 eq17134
    | exact resolve eq17134 eq16955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16955 eq17134
  have eq17138 : False := by grind
  exact eq17138

/-- `x □ y = if m(X,Y) = m(Y,Y) then m(X,X) else if X = Y then m(Y,X) else if m(X,X) = m(X,Y) then m(Y,Y)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxy_pyy_x_y_pxx_pxy_pxx_pyx_pyy_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a b = M.op b b ∨ a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 X0 y
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
  have eq51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq51 (σ X0)
       grind)
    | exact superpose eq51 eq10
    | exact resolve eq10 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq51 x
       grind)
    | exact superpose eq51 eq44
    | exact resolve eq44 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq55 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq54
       have i₂ := eq51 sF2
       grind)
    | exact superpose eq51 eq54
    | exact resolve eq54 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq56 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq53 X0
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq61 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq70 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
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
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq70
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq70
    | exact resolve eq70 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq21 eq72
    | exact resolve eq72 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq74 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq73
    | exact resolve eq73 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq74
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq74
    | exact resolve eq74 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq76 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq51 sF2
       grind)
    | exact superpose eq51 eq50
    | exact resolve eq50 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq77 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq76
       have i₂ := eq51 x
       grind)
    | exact superpose eq51 eq76
    | exact resolve eq76 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq87 : (M.op x y) ≠ (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op y y) ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq103 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq99
       have i₂ := eq51 sF3
       grind)
    | exact superpose eq51 eq99
    | exact resolve eq99 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq105 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq103
       have i₂ := eq51 y
       grind)
    | exact superpose eq51 eq103
    | exact resolve eq103 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq103
  have eq123 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq105
       grind)
    | exact superpose eq105 eq16
    | exact resolve eq16 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq569 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 X1
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq66
    | (have j0 := eq66 X0 X1
       grind)
    | exact resolve eq66 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq570 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq569 X0 X1
       have i₂ := eq56 X1
       grind)
    | exact superpose eq56 eq569
    | (have j0 := eq569 X0 X1
       grind)
    | exact resolve eq569 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq692 : ∀ X0 : G, (σ (M.op y y)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq570 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq570
    | (have j0 := eq570 X0 y
       grind)
    | exact resolve eq570 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq712 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq570 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq713 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq570 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq719 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq692 X0
       have i₂ := eq105
       grind)
    | exact superpose eq105 eq692
    | (have j0 := eq692 X0
       grind)
    | exact resolve eq692 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq3354 : ∀ X0 : G, (σ (k X0 y)) ≠ (M.op (σ y) (σ y)) ∨ (k (σ X0) (σ y)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | exact superpose eq719 eq14
    | (have j0 := eq14 (σ X0) (σ y)
       have j1 := eq719 X0
       grind)
    | (have r₁ := eq14 (σ y) (σ y)
       have r₂ := eq719 y
       grind)
    | (have r₁ := eq14 (σ X0) (σ y)
       have r₂ := eq719 X0
       grind)
    | exact resolve eq14 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3355 : ∀ X0 : G, (σ (k X0 y)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have j0 := eq719 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq3357 : ∀ X0 : G, (σ (k X0 y)) ≠ (M.op (σ y) (σ y)) ∨ (k (σ X0) (σ y)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have j0 := eq3354 X0
       have j1 := eq14 (σ X0) (σ y)
       grind)
    | (have r₁ := eq3354 y
       have r₂ := eq14 (σ y) (σ y)
       grind)
    | (have r₁ := eq3354 X0
       have r₂ := eq14 (σ X0) (σ y)
       grind)
    | exact resolve eq3354 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3354
  have eq3377 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (M.op X0 X0)) ∨ (σ (k X0 y)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq3357 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq3357
    | (have j0 := eq3357 X0
       grind)
    | exact resolve eq3357 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq3357
  have eq3386 : ∀ X0 : G, (σ (k X0 y)) ≠ (M.op (σ y) (σ y)) ∨ (σ (k X0 y)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | exact superpose eq41 eq3377
    | (have j0 := eq3377 X0
       grind)
    | exact resolve eq3377 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq3377
  have eq5505 : ∀ X0 : G, (M.op (σ y) (σ y)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq712 X0 y
       have i₂ := eq105
       grind)
    | exact superpose eq105 eq712
    | (have j0 := eq712 X0 y
       grind)
    | exact resolve eq712 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq5509 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ y)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq5505 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq5505
    | (have j0 := eq5505 X0
       grind)
    | exact resolve eq5505 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5505
  have eq5519 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ y)) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq5509 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq5509
    | (have j0 := eq5509 X0
       grind)
    | exact resolve eq5509 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5509
  have eq5529 : ∀ X0 : G, (M.op (σ y) (σ y)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq5519 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq5519
    | (have j0 := eq5519 X0
       grind)
    | exact resolve eq5519 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5519
  have eq23601 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq75 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23602 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq23601
    | exact resolve eq23601 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23601
  have eq23613 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq23602
       have r₂ := eq28
       grind)
    | exact resolve eq23602 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23602
  have eq23617 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq23613
    | exact resolve eq23613 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23613
  have eq23619 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq23617
    | exact resolve eq23617 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23617
  have eq23631 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq23619 eq14
    | (have j0 := eq14 X0 (σ y)
       grind)
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq23619
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq23619
       grind)
    | exact resolve eq14 eq23619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23619
  have eq31537 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq23631
    | (have j0 := eq23631 (σ x)
       grind)
    | (have r₁ := eq23631 (σ x)
       have r₂ := eq27
       grind)
    | exact resolve eq23631 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23631
  have eq31541 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq31537
  have eq31829 : (k x y) = (τ (M.op (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq31541 eq61
    | exact resolve eq61 eq31541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31541
  have eq31852 : (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq77 eq31829
    | exact resolve eq31829 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31829
  have eq32492 : (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq31852
       grind)
    | exact superpose eq31852 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq31852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31852
  have eq32493 : (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq32492
  have eq32496 : (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq32493
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq32493
    | exact resolve eq32493 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32493
  have eq32497 : (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq32496
  have eq32511 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq32497
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq32497
    | exact resolve eq32497 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32497
  have eq32512 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq32511
  have eq32525 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq32512 eq88
    | (have r₁ := eq88
       have r₂ := eq32512
       grind)
    | exact resolve eq88 eq32512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32540 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op y y) := by grind
  clear eq32525
  have eq32541 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op y y) := by grind
  clear eq32540
  have eq42482 : (k x y) = (τ (M.op (σ y) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq32541 eq61
    | exact resolve eq61 eq32541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32541
  have eq42508 : (k x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq123 eq42482
    | exact resolve eq42482 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq42482
  have eq42514 : (k x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq42508
       have r₂ := eq87
       grind)
    | exact resolve eq42508 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42508
  have eq42529 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq713 x y
       have i₂ := eq42514
       grind)
    | exact superpose eq42514 eq713
    | (have j0 := eq713 x y
       grind)
    | exact resolve eq713 eq42514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq42530 : (M.op x y) = (M.op y y) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq42514
       grind)
    | exact superpose eq42514 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq42514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42514
  have eq42531 : (M.op x y) = (M.op y y) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq42530
  have eq42532 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by grind
  clear eq42529
  have eq42536 : (M.op x y) = (M.op y y) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq42531
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq42531
    | exact resolve eq42531 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42531
  have eq42537 : (M.op x y) = (M.op y y) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq42536
  have eq42538 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq42532
       have i₂ := eq55
       grind)
    | exact superpose eq55 eq42532
    | exact resolve eq42532 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42532
  have eq42551 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq42537
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq42537
    | exact resolve eq42537 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42537
  have eq42552 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq42538
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq42538
    | exact resolve eq42538 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42538
  have eq42554 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq42552
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq42552
    | exact resolve eq42552 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42552
  have eq42555 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq27 eq42554
    | exact resolve eq42554 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42554
  have eq42556 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq42555
       have i₂ := eq105
       grind)
    | exact superpose eq105 eq42555
    | exact resolve eq42555 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42555
  have eq42557 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq42556
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq42556
    | exact resolve eq42556 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42556
  have eq42558 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq42557
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq42557
    | exact resolve eq42557 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42557
  have eq42559 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq27 eq42558
    | exact resolve eq42558 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42558
  have eq42560 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by grind
  clear eq42559
  have eq42561 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq42560
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq42560
    | exact resolve eq42560 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42560
  have eq42562 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq42561
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq42561
    | exact resolve eq42561 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42561
  have eq42563 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op y y) := by grind
  clear eq42562
  have eq42575 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq42551 eq14
    | (have j0 := eq14 X0 (σ y)
       grind)
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq42551
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq42551
       grind)
    | exact resolve eq14 eq42551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42551
  have eq66576 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq42575
    | (have j0 := eq42575 (σ x)
       grind)
    | (have r₁ := eq42575 (σ x)
       have r₂ := eq27
       grind)
    | exact resolve eq42575 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42575
  have eq66586 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq66576
  have eq66598 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq66586 eq75
    | exact resolve eq75 eq66586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq66586
  have eq66625 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq66598
  have eq66653 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq66625 eq32512
    | exact resolve eq32512 eq66625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32512 eq66625
  have eq66716 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq66653
  have eq66723 : (M.op x y) = (M.op y y) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq66716
       have r₂ := eq28
       grind)
    | exact resolve eq66716 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66716
  have eq66741 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq105
       have i₂ := eq66723
       grind)
    | exact superpose eq66723 eq105
    | exact resolve eq105 eq66723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66754 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y
       have i₂ := eq66723
       grind)
    | exact superpose eq66723 eq14
    | (have j0 := eq14 X0 y
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq66723
       grind)
    | exact resolve eq14 eq66723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66723
  have eq66776 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq66741
    | exact resolve eq66741 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66741
  have eq82889 : (M.op x y) ≠ (M.op x y) ∨ (k x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq66754 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq66754
    | (have j0 := eq66754 x
       grind)
    | (have r₁ := eq66754 x
       have r₂ := eq19
       grind)
    | exact resolve eq66754 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66754
  have eq82899 : (k x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq82889
  have eq82903 : (k (σ x) (σ y)) = (σ (M.op x x)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq82899
       grind)
    | exact superpose eq82899 eq45
    | exact resolve eq45 eq82899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82899
  have eq82952 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq82903
       have i₂ := eq55
       grind)
    | exact superpose eq55 eq82903
    | exact resolve eq82903 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82903
  have eq82989 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq82952 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq82952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82990 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by grind
  clear eq82989
  have eq83005 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq27 eq82990
    | exact resolve eq82990 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82990
  have eq83016 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq27 eq83005
    | exact resolve eq83005 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83005
  have eq83039 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq83016 eq66776
    | exact resolve eq66776 eq83016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83016
  have eq83086 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq83039
  have eq83100 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq83086
       have r₂ := eq28
       grind)
    | exact resolve eq83086 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83086
  have eq83104 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq83100 eq88
    | (have r₁ := eq88
       have r₂ := eq83100
       grind)
    | exact resolve eq88 eq83100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq83134 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq83104
  have eq83135 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq83134
  have eq107218 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq83135 eq82952
    | exact resolve eq82952 eq83135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82952 eq83135
  have eq107223 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
  clear eq107218
  have eq107372 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
  clear eq107223
  have eq107477 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq107372
       have r₂ := eq83100
       grind)
    | exact resolve eq107372 eq83100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83100 eq107372
  have eq107514 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq107477 eq66776
    | exact resolve eq66776 eq107477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66776 eq107477
  have eq107565 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq107514
  have eq107581 : (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq107565
       have r₂ := eq28
       grind)
    | exact resolve eq107565 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107565
  have eq107586 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq55
       have i₂ := eq107581
       grind)
    | exact superpose eq107581 eq55
    | exact resolve eq55 eq107581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107587 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (M.op y y) ∨ (k x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq87
       have i₂ := eq107581
       grind)
    | exact superpose eq107581 eq87
    | (have r₁ := eq87
       have r₂ := eq107581
       grind)
    | exact resolve eq87 eq107581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq107607 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (M.op y y) ∨ (k x y) = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq107587
  have eq107608 : (k x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq107607
  have eq107628 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq107586
    | exact resolve eq107586 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107586
  have eq281657 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3386 x
       have i₂ := eq107608
       grind)
    | exact superpose eq107608 eq3386
    | (have j0 := eq3386 x
       grind)
    | exact resolve eq3386 eq107608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107608
  have eq281802 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq281657
       have r₂ := eq105
       grind)
    | exact resolve eq281657 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281657
  have eq281856 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq281802
       have i₂ := eq105
       grind)
    | exact superpose eq105 eq281802
    | exact resolve eq281802 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281802
  have eq281904 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq281856
       have i₂ := eq55
       grind)
    | exact superpose eq55 eq281856
    | exact resolve eq281856 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281856
  have eq281952 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq281904
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq281904
    | exact resolve eq281904 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281904
  have eq281972 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq281952
       have i₂ := eq55
       grind)
    | exact superpose eq55 eq281952
    | exact resolve eq281952 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281952
  have eq281990 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq281972
    | exact resolve eq281972 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281972
  have eq282003 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq281990
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq281990
    | exact resolve eq281990 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281990
  have eq282004 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq282003
  have eq288587 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5529 x
       have i₂ := eq107581
       grind)
    | exact superpose eq107581 eq5529
    | (have j0 := eq5529 x
       grind)
    | exact resolve eq5529 eq107581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5529 eq107581
  have eq288674 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq288587
    | exact resolve eq288587 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288587
  have eq288709 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq288674
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq288674
    | exact resolve eq288674 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288674
  have eq288744 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq288709
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq288709
    | exact resolve eq288709 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq288709
  have eq288778 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq288744
    | exact resolve eq288744 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288744
  have eq288784 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq288778
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq288778
    | exact resolve eq288778 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288778
  have eq288789 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq288784
    | exact resolve eq288784 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288784
  have eq288793 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq288789
    | exact resolve eq288789 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288789
  have eq288795 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq288793
       have r₂ := eq28
       grind)
    | exact resolve eq288793 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288793
  have eq288796 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq288795
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq288795
    | exact resolve eq288795 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288795
  have eq288797 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq288796
  have eq946903 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq282004 eq42563
    | exact resolve eq42563 eq282004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42563 eq282004
  have eq947083 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by grind
  clear eq946903
  have eq947157 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq947083 eq107628
    | exact resolve eq107628 eq947083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947083
  have eq947709 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq947157
  have eq947730 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq947709
       have r₂ := eq28
       grind)
    | exact resolve eq947709 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947709
  have eq947735 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq105
       have i₂ := eq947730
       grind)
    | exact superpose eq947730 eq105
    | exact resolve eq105 eq947730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq947759 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq14 X0 y
       have i₂ := eq947730
       grind)
    | exact superpose eq947730 eq14
    | (have j0 := eq14 X0 y
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq947730
       grind)
    | exact resolve eq14 eq947730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947730
  have eq947808 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq947735
    | exact resolve eq947735 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947735
  have eq947954 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq947808 eq288797
    | (have r₁ := eq288797
       have r₂ := eq947808
       grind)
    | exact resolve eq288797 eq947808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288797 eq947808
  have eq947983 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq947954
  have eq947984 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq947983
  have eq948097 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq947984 eq61
    | exact resolve eq61 eq947984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq947984
  have eq948225 : (M.op (σ y) (σ y)) ≠ (σ (τ (M.op (σ x) (σ y)))) ∨ (σ (M.op x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ (M.op x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3386 x
       have i₂ := eq948097
       grind)
    | exact superpose eq948097 eq3386
    | (have j0 := eq3386 x
       grind)
    | exact resolve eq3386 eq948097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3386 eq948097
  have eq948276 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ (M.op x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq948225
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq948225
    | exact resolve eq948225 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948225
  have eq948306 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq948276
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq948276
    | exact resolve eq948276 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948276
  have eq948326 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq948306
       have i₂ := eq55
       grind)
    | exact superpose eq55 eq948306
    | exact resolve eq948306 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948306
  have eq948337 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq948326
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq948326
    | exact resolve eq948326 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948326
  have eq948348 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq948337
       have i₂ := eq55
       grind)
    | exact superpose eq55 eq948337
    | exact resolve eq948337 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948337
  have eq948355 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq948348
    | exact resolve eq948348 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948348
  have eq948356 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq948355
  have eq948361 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq948356
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq948356
    | exact resolve eq948356 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948356
  have eq948362 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq948361
  have eq1035460 : (M.op x y) ≠ (M.op x y) ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq947759 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq947759
    | (have j0 := eq947759 x
       grind)
    | (have r₁ := eq947759 x
       have r₂ := eq19
       grind)
    | exact resolve eq947759 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947759
  have eq1035473 : (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1035460
  have eq1035522 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3355 x
       have i₂ := eq1035473
       grind)
    | exact superpose eq1035473 eq3355
    | (have j0 := eq3355 x
       grind)
    | exact resolve eq3355 eq1035473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3355 eq1035473
  have eq1035536 : (σ (M.op x x)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1035522
  have eq1035575 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1035536
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1035536
    | exact resolve eq1035536 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035536
  have eq1035599 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1035575
       have i₂ := eq55
       grind)
    | exact superpose eq55 eq1035575
    | exact resolve eq1035575 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq1035575
  have eq1035608 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq1035599
    | exact resolve eq1035599 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035599
  have eq1035615 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1035608
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1035608
    | exact resolve eq1035608 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035608
  have eq1035622 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq1035615
    | exact resolve eq1035615 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035615
  have eq1035628 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1035622
       have r₂ := eq948362
       grind)
    | exact resolve eq1035622 eq948362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948362 eq1035622
  have eq1035634 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1035628
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1035628
    | exact resolve eq1035628 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035628
  have eq1035635 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1035634
  have eq1035676 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1035635 eq107628
    | exact resolve eq107628 eq1035635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107628 eq1035635
  have eq1036234 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1035676
  have eq1036256 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1036234
       have r₂ := eq28
       grind)
    | exact resolve eq1036234 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036234
  have eq1036261 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1036256 eq30
    | exact resolve eq30 eq1036256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1036256
  have eq1036525 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq1036261
    | exact resolve eq1036261 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1036261
  have eq1036526 : x = y := by grind
  clear eq1036525
  have eq1036573 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1036526
       grind)
    | exact superpose eq1036526 eq19
    | exact resolve eq19 eq1036526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1036574 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1036526
       grind)
    | exact superpose eq1036526 eq25
    | exact resolve eq25 eq1036526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1036526
  have eq1036966 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1036574
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1036574
    | exact resolve eq1036574 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1036574
  have eq1036997 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1036966 eq27
    | exact resolve eq27 eq1036966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1036966
  have eq1039930 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1036997 eq77
    | exact resolve eq77 eq1036997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq1036997
  have eq1040271 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1039930
       have i₂ := eq1036573
       grind)
    | exact superpose eq1036573 eq1039930
    | exact resolve eq1039930 eq1036573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036573 eq1039930
  have eq1040300 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1040271 eq15
    | exact resolve eq15 eq1040271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040271
  have eq1040923 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1040300
    | exact resolve eq1040300 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1040300
  have eq1041077 : False := by grind
  exact eq1041077

/-- `x □ y = if m(X,Y) = m(Y,Y) then m(X,X) else if X = Y then m(Y,Y) else if m(X,X) = m(X,Y) then m(Y,Y)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxy_pyy_x_y_pxx_pxy_pxx_pyy_pyy_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a b = M.op b b ∨ a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 X0 y
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
  have eq51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq51 (σ X0)
       grind)
    | exact superpose eq51 eq10
    | exact resolve eq10 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq51 x
       grind)
    | exact superpose eq51 eq44
    | exact resolve eq44 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq55 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq54
       have i₂ := eq51 sF2
       grind)
    | exact superpose eq51 eq54
    | exact resolve eq54 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq56 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq53 X0
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq61 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq70 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
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
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq70
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq70
    | exact resolve eq70 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq21 eq72
    | exact resolve eq72 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq74 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq73
    | exact resolve eq73 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq74
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq74
    | exact resolve eq74 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq76 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq51 sF2
       grind)
    | exact superpose eq51 eq50
    | exact resolve eq50 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq77 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq76
       have i₂ := eq51 x
       grind)
    | exact superpose eq51 eq76
    | exact resolve eq76 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq87 : (M.op x y) ≠ (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op y y) ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq103 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq99
       have i₂ := eq51 sF3
       grind)
    | exact superpose eq51 eq99
    | exact resolve eq99 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq105 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq103
       have i₂ := eq51 y
       grind)
    | exact superpose eq51 eq103
    | exact resolve eq103 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq103
  have eq123 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq105
       grind)
    | exact superpose eq105 eq16
    | exact resolve eq16 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq569 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 X1
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq66
    | (have j0 := eq66 X0 X1
       grind)
    | exact resolve eq66 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq570 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq569 X0 X1
       have i₂ := eq56 X1
       grind)
    | exact superpose eq56 eq569
    | (have j0 := eq569 X0 X1
       grind)
    | exact resolve eq569 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq692 : ∀ X0 : G, (σ (M.op y y)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq570 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq570
    | (have j0 := eq570 X0 y
       grind)
    | exact resolve eq570 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq712 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq570 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq713 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq570 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq719 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq692 X0
       have i₂ := eq105
       grind)
    | exact superpose eq105 eq692
    | (have j0 := eq692 X0
       grind)
    | exact resolve eq692 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq3354 : ∀ X0 : G, (σ (k X0 y)) ≠ (M.op (σ y) (σ y)) ∨ (k (σ X0) (σ y)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | exact superpose eq719 eq14
    | (have j0 := eq14 (σ X0) (σ y)
       have j1 := eq719 X0
       grind)
    | (have r₁ := eq14 (σ y) (σ y)
       have r₂ := eq719 y
       grind)
    | (have r₁ := eq14 (σ X0) (σ y)
       have r₂ := eq719 X0
       grind)
    | exact resolve eq14 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3355 : ∀ X0 : G, (σ (k X0 y)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have j0 := eq719 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq3357 : ∀ X0 : G, (σ (k X0 y)) ≠ (M.op (σ y) (σ y)) ∨ (k (σ X0) (σ y)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have j0 := eq3354 X0
       have j1 := eq14 (σ X0) (σ y)
       grind)
    | (have r₁ := eq3354 y
       have r₂ := eq14 (σ y) (σ y)
       grind)
    | (have r₁ := eq3354 X0
       have r₂ := eq14 (σ X0) (σ y)
       grind)
    | exact resolve eq3354 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3354
  have eq3377 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (M.op X0 X0)) ∨ (σ (k X0 y)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq3357 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq3357
    | (have j0 := eq3357 X0
       grind)
    | exact resolve eq3357 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq3357
  have eq3386 : ∀ X0 : G, (σ (k X0 y)) ≠ (M.op (σ y) (σ y)) ∨ (σ (k X0 y)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | exact superpose eq41 eq3377
    | (have j0 := eq3377 X0
       grind)
    | exact resolve eq3377 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq3377
  have eq5505 : ∀ X0 : G, (M.op (σ y) (σ y)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq712 X0 y
       have i₂ := eq105
       grind)
    | exact superpose eq105 eq712
    | (have j0 := eq712 X0 y
       grind)
    | exact resolve eq712 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq5509 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ y)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq5505 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq5505
    | (have j0 := eq5505 X0
       grind)
    | exact resolve eq5505 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5505
  have eq5519 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ y)) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq5509 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq5509
    | (have j0 := eq5509 X0
       grind)
    | exact resolve eq5509 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5509
  have eq5529 : ∀ X0 : G, (M.op (σ y) (σ y)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq5519 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq5519
    | (have j0 := eq5519 X0
       grind)
    | exact resolve eq5519 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5519
  have eq23601 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq75 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23602 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq23601
    | exact resolve eq23601 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23601
  have eq23613 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq23602
       have r₂ := eq28
       grind)
    | exact resolve eq23602 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23602
  have eq23617 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq23613
    | exact resolve eq23613 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23613
  have eq23619 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq23617
    | exact resolve eq23617 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23617
  have eq23631 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq23619 eq14
    | (have j0 := eq14 X0 (σ y)
       grind)
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq23619
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq23619
       grind)
    | exact resolve eq14 eq23619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23619
  have eq31537 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq23631
    | (have j0 := eq23631 (σ x)
       grind)
    | (have r₁ := eq23631 (σ x)
       have r₂ := eq27
       grind)
    | exact resolve eq23631 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23631
  have eq31541 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq31537
  have eq31829 : (k x y) = (τ (M.op (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq31541 eq61
    | exact resolve eq61 eq31541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31541
  have eq31852 : (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq77 eq31829
    | exact resolve eq31829 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31829
  have eq32492 : (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq31852
       grind)
    | exact superpose eq31852 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq31852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31852
  have eq32493 : (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq32492
  have eq32496 : (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq32493
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq32493
    | exact resolve eq32493 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32493
  have eq32497 : (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq32496
  have eq32511 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq32497
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq32497
    | exact resolve eq32497 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32497
  have eq32512 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq32511
  have eq32525 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq32512 eq88
    | (have r₁ := eq88
       have r₂ := eq32512
       grind)
    | exact resolve eq88 eq32512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32540 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op y y) := by grind
  clear eq32525
  have eq32541 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op y y) := by grind
  clear eq32540
  have eq42482 : (k x y) = (τ (M.op (σ y) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq32541 eq61
    | exact resolve eq61 eq32541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32541
  have eq42508 : (k x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq123 eq42482
    | exact resolve eq42482 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq42482
  have eq42514 : (k x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq42508
       have r₂ := eq87
       grind)
    | exact resolve eq42508 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42508
  have eq42529 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq713 x y
       have i₂ := eq42514
       grind)
    | exact superpose eq42514 eq713
    | (have j0 := eq713 x y
       grind)
    | exact resolve eq713 eq42514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq42530 : (M.op x y) = (M.op y y) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq42514
       grind)
    | exact superpose eq42514 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq42514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42514
  have eq42531 : (M.op x y) = (M.op y y) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq42530
  have eq42532 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by grind
  clear eq42529
  have eq42536 : (M.op x y) = (M.op y y) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq42531
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq42531
    | exact resolve eq42531 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42531
  have eq42537 : (M.op x y) = (M.op y y) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq42536
  have eq42538 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq42532
       have i₂ := eq55
       grind)
    | exact superpose eq55 eq42532
    | exact resolve eq42532 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42532
  have eq42551 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq42537
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq42537
    | exact resolve eq42537 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42537
  have eq42552 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq42538
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq42538
    | exact resolve eq42538 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42538
  have eq42554 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq42552
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq42552
    | exact resolve eq42552 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42552
  have eq42555 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq27 eq42554
    | exact resolve eq42554 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42554
  have eq42556 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq42555
       have i₂ := eq105
       grind)
    | exact superpose eq105 eq42555
    | exact resolve eq42555 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42555
  have eq42557 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq42556
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq42556
    | exact resolve eq42556 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42556
  have eq42558 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq42557
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq42557
    | exact resolve eq42557 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42557
  have eq42559 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq27 eq42558
    | exact resolve eq42558 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42558
  have eq42560 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by grind
  clear eq42559
  have eq42561 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq42560
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq42560
    | exact resolve eq42560 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42560
  have eq42562 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq42561
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq42561
    | exact resolve eq42561 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42561
  have eq42563 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op y y) := by grind
  clear eq42562
  have eq42575 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq42551 eq14
    | (have j0 := eq14 X0 (σ y)
       grind)
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq42551
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq42551
       grind)
    | exact resolve eq14 eq42551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42551
  have eq66576 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq42575
    | (have j0 := eq42575 (σ x)
       grind)
    | (have r₁ := eq42575 (σ x)
       have r₂ := eq27
       grind)
    | exact resolve eq42575 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42575
  have eq66586 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq66576
  have eq66598 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq66586 eq75
    | exact resolve eq75 eq66586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq66586
  have eq66625 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq66598
  have eq66653 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq66625 eq32512
    | exact resolve eq32512 eq66625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32512 eq66625
  have eq66716 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq66653
  have eq66723 : (M.op x y) = (M.op y y) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq66716
       have r₂ := eq28
       grind)
    | exact resolve eq66716 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66716
  have eq66741 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq105
       have i₂ := eq66723
       grind)
    | exact superpose eq66723 eq105
    | exact resolve eq105 eq66723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66754 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y
       have i₂ := eq66723
       grind)
    | exact superpose eq66723 eq14
    | (have j0 := eq14 X0 y
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq66723
       grind)
    | exact resolve eq14 eq66723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66723
  have eq66776 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq66741
    | exact resolve eq66741 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66741
  have eq82889 : (M.op x y) ≠ (M.op x y) ∨ (k x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq66754 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq66754
    | (have j0 := eq66754 x
       grind)
    | (have r₁ := eq66754 x
       have r₂ := eq19
       grind)
    | exact resolve eq66754 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66754
  have eq82899 : (k x y) = (M.op x x) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq82889
  have eq82903 : (k (σ x) (σ y)) = (σ (M.op x x)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq82899
       grind)
    | exact superpose eq82899 eq45
    | exact resolve eq45 eq82899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82899
  have eq82952 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq82903
       have i₂ := eq55
       grind)
    | exact superpose eq55 eq82903
    | exact resolve eq82903 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82903
  have eq82989 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq82952 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq82952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82990 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by grind
  clear eq82989
  have eq83005 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq27 eq82990
    | exact resolve eq82990 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82990
  have eq83016 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq27 eq83005
    | exact resolve eq83005 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83005
  have eq83039 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq83016 eq66776
    | exact resolve eq66776 eq83016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83016
  have eq83086 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq83039
  have eq83100 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq83086
       have r₂ := eq28
       grind)
    | exact resolve eq83086 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83086
  have eq83104 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq83100 eq88
    | (have r₁ := eq88
       have r₂ := eq83100
       grind)
    | exact resolve eq88 eq83100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq83134 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq83104
  have eq83135 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq83134
  have eq107218 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq83135 eq82952
    | exact resolve eq82952 eq83135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82952 eq83135
  have eq107223 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
  clear eq107218
  have eq107372 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
  clear eq107223
  have eq107477 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq107372
       have r₂ := eq83100
       grind)
    | exact resolve eq107372 eq83100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83100 eq107372
  have eq107514 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq107477 eq66776
    | exact resolve eq66776 eq107477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66776 eq107477
  have eq107565 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq107514
  have eq107581 : (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq107565
       have r₂ := eq28
       grind)
    | exact resolve eq107565 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107565
  have eq107586 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq55
       have i₂ := eq107581
       grind)
    | exact superpose eq107581 eq55
    | exact resolve eq55 eq107581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107587 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (M.op y y) ∨ (k x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq87
       have i₂ := eq107581
       grind)
    | exact superpose eq107581 eq87
    | (have r₁ := eq87
       have r₂ := eq107581
       grind)
    | exact resolve eq87 eq107581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq107607 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (M.op y y) ∨ (k x y) = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq107587
  have eq107608 : (k x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq107607
  have eq107628 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq107586
    | exact resolve eq107586 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107586
  have eq281657 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3386 x
       have i₂ := eq107608
       grind)
    | exact superpose eq107608 eq3386
    | (have j0 := eq3386 x
       grind)
    | exact resolve eq3386 eq107608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107608
  have eq281802 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq281657
       have r₂ := eq105
       grind)
    | exact resolve eq281657 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281657
  have eq281856 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq281802
       have i₂ := eq105
       grind)
    | exact superpose eq105 eq281802
    | exact resolve eq281802 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281802
  have eq281904 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq281856
       have i₂ := eq55
       grind)
    | exact superpose eq55 eq281856
    | exact resolve eq281856 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281856
  have eq281952 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq281904
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq281904
    | exact resolve eq281904 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281904
  have eq281972 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq281952
       have i₂ := eq55
       grind)
    | exact superpose eq55 eq281952
    | exact resolve eq281952 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281952
  have eq281990 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq281972
    | exact resolve eq281972 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281972
  have eq282003 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq281990
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq281990
    | exact resolve eq281990 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281990
  have eq282004 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq282003
  have eq288587 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5529 x
       have i₂ := eq107581
       grind)
    | exact superpose eq107581 eq5529
    | (have j0 := eq5529 x
       grind)
    | exact resolve eq5529 eq107581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5529 eq107581
  have eq288674 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq288587
    | exact resolve eq288587 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288587
  have eq288709 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq288674
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq288674
    | exact resolve eq288674 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288674
  have eq288744 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq288709
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq288709
    | exact resolve eq288709 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq288709
  have eq288778 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq288744
    | exact resolve eq288744 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288744
  have eq288784 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq288778
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq288778
    | exact resolve eq288778 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288778
  have eq288789 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq288784
    | exact resolve eq288784 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288784
  have eq288793 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq288789
    | exact resolve eq288789 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288789
  have eq288795 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq288793
       have r₂ := eq28
       grind)
    | exact resolve eq288793 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288793
  have eq288796 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq288795
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq288795
    | exact resolve eq288795 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288795
  have eq288797 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq288796
  have eq946903 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq282004 eq42563
    | exact resolve eq42563 eq282004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42563 eq282004
  have eq947083 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by grind
  clear eq946903
  have eq947157 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq947083 eq107628
    | exact resolve eq107628 eq947083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947083
  have eq947709 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq947157
  have eq947730 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq947709
       have r₂ := eq28
       grind)
    | exact resolve eq947709 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947709
  have eq947735 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq105
       have i₂ := eq947730
       grind)
    | exact superpose eq947730 eq105
    | exact resolve eq105 eq947730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq947759 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq14 X0 y
       have i₂ := eq947730
       grind)
    | exact superpose eq947730 eq14
    | (have j0 := eq14 X0 y
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq947730
       grind)
    | exact resolve eq14 eq947730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947730
  have eq947808 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq947735
    | exact resolve eq947735 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947735
  have eq947954 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq947808 eq288797
    | (have r₁ := eq288797
       have r₂ := eq947808
       grind)
    | exact resolve eq288797 eq947808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288797 eq947808
  have eq947983 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq947954
  have eq947984 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq947983
  have eq948097 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq947984 eq61
    | exact resolve eq61 eq947984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq947984
  have eq948225 : (M.op (σ y) (σ y)) ≠ (σ (τ (M.op (σ x) (σ y)))) ∨ (σ (M.op x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ (M.op x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3386 x
       have i₂ := eq948097
       grind)
    | exact superpose eq948097 eq3386
    | (have j0 := eq3386 x
       grind)
    | exact resolve eq3386 eq948097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3386 eq948097
  have eq948276 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op x x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ (M.op x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq948225
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq948225
    | exact resolve eq948225 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948225
  have eq948306 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq948276
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq948276
    | exact resolve eq948276 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948276
  have eq948326 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq948306
       have i₂ := eq55
       grind)
    | exact superpose eq55 eq948306
    | exact resolve eq948306 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948306
  have eq948337 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq948326
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq948326
    | exact resolve eq948326 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948326
  have eq948348 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq948337
       have i₂ := eq55
       grind)
    | exact superpose eq55 eq948337
    | exact resolve eq948337 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948337
  have eq948355 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq948348
    | exact resolve eq948348 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948348
  have eq948356 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq948355
  have eq948361 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq948356
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq948356
    | exact resolve eq948356 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948356
  have eq948362 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq948361
  have eq1035460 : (M.op x y) ≠ (M.op x y) ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq947759 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq947759
    | (have j0 := eq947759 x
       grind)
    | (have r₁ := eq947759 x
       have r₂ := eq19
       grind)
    | exact resolve eq947759 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947759
  have eq1035473 : (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1035460
  have eq1035522 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3355 x
       have i₂ := eq1035473
       grind)
    | exact superpose eq1035473 eq3355
    | (have j0 := eq3355 x
       grind)
    | exact resolve eq3355 eq1035473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3355 eq1035473
  have eq1035536 : (σ (M.op x x)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1035522
  have eq1035575 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1035536
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1035536
    | exact resolve eq1035536 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035536
  have eq1035599 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1035575
       have i₂ := eq55
       grind)
    | exact superpose eq55 eq1035575
    | exact resolve eq1035575 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq1035575
  have eq1035608 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq1035599
    | exact resolve eq1035599 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035599
  have eq1035615 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1035608
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1035608
    | exact resolve eq1035608 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035608
  have eq1035622 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq1035615
    | exact resolve eq1035615 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035615
  have eq1035628 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1035622
       have r₂ := eq948362
       grind)
    | exact resolve eq1035622 eq948362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948362 eq1035622
  have eq1035634 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1035628
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1035628
    | exact resolve eq1035628 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035628
  have eq1035635 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1035634
  have eq1035676 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1035635 eq107628
    | exact resolve eq107628 eq1035635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107628 eq1035635
  have eq1036234 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1035676
  have eq1036256 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1036234
       have r₂ := eq28
       grind)
    | exact resolve eq1036234 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036234
  have eq1036261 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1036256 eq30
    | exact resolve eq30 eq1036256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1036256
  have eq1036525 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq1036261
    | exact resolve eq1036261 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1036261
  have eq1036526 : x = y := by grind
  clear eq1036525
  have eq1036573 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1036526
       grind)
    | exact superpose eq1036526 eq19
    | exact resolve eq19 eq1036526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1036574 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1036526
       grind)
    | exact superpose eq1036526 eq25
    | exact resolve eq25 eq1036526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1036526
  have eq1036966 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1036574
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1036574
    | exact resolve eq1036574 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1036574
  have eq1036997 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1036966 eq27
    | exact resolve eq27 eq1036966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1036966
  have eq1039930 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1036997 eq77
    | exact resolve eq77 eq1036997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq1036997
  have eq1040271 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1039930
       have i₂ := eq1036573
       grind)
    | exact superpose eq1036573 eq1039930
    | exact resolve eq1039930 eq1036573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036573 eq1039930
  have eq1040300 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1040271 eq15
    | exact resolve eq15 eq1040271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040271
  have eq1040923 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1040300
    | exact resolve eq1040300 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1040300
  have eq1041077 : False := by grind
  exact eq1041077

/-- `x □ y = if m(X,Y) = X then Y else if m(X,Y) = Y then X else if m(X,X) = m(X,Y) then m(X,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxy_x_pxy_y_pxx_pxy_y_x_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a b = a ∨ M.op a b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
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
  have eq50 : x ≠ (M.op x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
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
  have eq56 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ x = (k x y) := by
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
  have eq57 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
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
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq68
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq68
    | exact resolve eq68 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq74 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq72
    | exact resolve eq72 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq76 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq74
    | exact resolve eq74 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq78 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq76
    | exact resolve eq76 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq78
    | exact resolve eq78 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq97 : (M.op x y) ≠ (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (k x y) = (M.op x x) := by
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
  have eq98 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq99 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq179 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq466 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq100 x
       grind)
    | exact superpose eq100 eq43
    | (have j1 := eq100 x
       grind)
    | exact resolve eq43 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq100
  have eq4427 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq179 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq179
    | (have j0 := eq179 x
       grind)
    | exact resolve eq179 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq4445 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq4427
    | exact resolve eq4427 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4427
  have eq4461 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq4445
    | exact resolve eq4445 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4445
  have eq4466 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4461
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq4461
    | exact resolve eq4461 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4461
  have eq4467 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq4466
    | exact resolve eq4466 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4466
  have eq4468 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq4467
    | exact resolve eq4467 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4467
  have eq15808 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq79 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15809 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq15808
    | exact resolve eq15808 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15808
  have eq15820 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq15809
       have r₂ := eq27
       grind)
    | exact resolve eq15809 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15809
  have eq15822 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq15820
    | exact resolve eq15820 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15820
  have eq15824 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq15822
    | exact resolve eq15822 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15822
  have eq15826 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq15824
    | exact resolve eq15824 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15824
  have eq15829 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15826 eq98
    | (have r₁ := eq98
       have r₂ := eq15826
       grind)
    | exact resolve eq98 eq15826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15826
  have eq15837 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq15829
  have eq15838 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq15837
  have eq15871 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15838 eq79
    | exact resolve eq79 eq15838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq15838
  have eq15879 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15871
  have eq15881 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq15879
       have r₂ := eq27
       grind)
    | exact resolve eq15879 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15879
  have eq15883 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq466
       have i₂ := eq15881
       grind)
    | exact superpose eq15881 eq466
    | exact resolve eq466 eq15881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq15884 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq97
       have i₂ := eq15881
       grind)
    | exact superpose eq15881 eq97
    | (have r₁ := eq97
       have r₂ := eq15881
       grind)
    | exact resolve eq97 eq15881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15881
  have eq15892 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15884
  have eq15893 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15892
  have eq15894 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15883
  have eq15895 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq15894
    | exact resolve eq15894 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15894
  have eq16090 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq15893
       grind)
    | exact superpose eq15893 eq44
    | exact resolve eq44 eq15893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15893
  have eq16108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq16090
    | exact resolve eq16090 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16090
  have eq16147 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16108 eq4468
    | exact resolve eq4468 eq16108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16108
  have eq16151 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq16147
  have eq16155 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq16151
       have r₂ := eq27
       grind)
    | exact resolve eq16151 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16151
  have eq16181 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16155 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq16155
       grind)
    | exact resolve eq12 eq16155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16155
  have eq16186 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq16181
  have eq16187 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq16186
  have eq16702 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16187 eq15895
    | exact resolve eq15895 eq16187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15895 eq16187
  have eq16706 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq16702
  have eq16708 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq16706
       have r₂ := eq27
       grind)
    | exact resolve eq16706 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16706
  have eq16710 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16708 eq57
    | (have r₁ := eq57
       have r₂ := eq16708
       grind)
    | exact resolve eq57 eq16708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq16713 : (σ x) ≠ (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16708
  have eq16714 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16710
  have eq17208 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq16714
       have r₂ := eq16713
       grind)
    | exact resolve eq16714 eq16713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16713 eq16714
  have eq17216 : (τ (σ x)) = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17208 eq55
    | exact resolve eq55 eq17208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17208
  have eq17246 : x = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq17216
    | exact resolve eq17216 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq17216
  have eq17252 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17246
       have r₂ := eq56
       grind)
    | exact resolve eq17246 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17246
  have eq17498 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq17252
       grind)
    | exact superpose eq17252 eq44
    | exact resolve eq44 eq17252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17508 : x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq17252
       grind)
    | exact superpose eq17252 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq17252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17509 : x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17508
  have eq17513 : x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17509
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17509
    | exact resolve eq17509 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17509
  have eq17514 : x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17513
  have eq17523 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17498
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17498
    | exact resolve eq17498 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17498
  have eq17526 : y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17514
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17514
    | exact resolve eq17514 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17514
  have eq17528 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17526
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17526
    | exact resolve eq17526 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17526
  have eq17545 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17523 eq4468
    | exact resolve eq4468 eq17523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17552 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17545
  have eq17577 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq97
       have i₂ := eq17528
       grind)
    | exact superpose eq17528 eq97
    | (have r₁ := eq97
       have r₂ := eq17528
       grind)
    | exact resolve eq97 eq17528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17528
  have eq17585 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17577
  have eq17586 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17585
  have eq17832 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17552 eq98
    | (have r₁ := eq98
       have r₂ := eq17552
       grind)
    | exact resolve eq98 eq17552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq17552
  have eq17840 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17832
  have eq17841 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17840
  have eq18380 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17252
       have i₂ := eq17586
       grind)
    | exact superpose eq17586 eq17252
    | exact resolve eq17252 eq17586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17252 eq17586
  have eq18382 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq18380
  have eq18394 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18382 eq51
    | (have r₁ := eq51
       have r₂ := eq18382
       grind)
    | exact resolve eq51 eq18382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18382
  have eq18396 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq18394
  have eq18657 : (τ (σ y)) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18396 eq55
    | exact resolve eq55 eq18396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18396
  have eq18692 : y = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq18657
    | exact resolve eq18657 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18657
  have eq18697 : y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq18692
       have r₂ := eq50
       grind)
    | exact resolve eq18692 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18692
  have eq18717 : y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18697
       grind)
    | exact superpose eq18697 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18718 : y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq18717
  have eq18724 : y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18718
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18718
    | exact resolve eq18718 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18718
  have eq18725 : y = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq18724
  have eq18737 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18725
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18725
    | exact resolve eq18725 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18725
  have eq18739 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18737
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18737
    | exact resolve eq18737 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq18737
  have eq19034 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq18739
       grind)
    | exact superpose eq18739 eq97
    | (have r₁ := eq97
       have r₂ := eq18739
       grind)
    | exact resolve eq97 eq18739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq18739
  have eq19042 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) := by grind
  clear eq19034
  have eq19043 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq19042
  have eq19326 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18697
       have i₂ := eq19043
       grind)
    | exact superpose eq19043 eq18697
    | exact resolve eq18697 eq19043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18697 eq19043
  have eq19328 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq19326
  have eq19341 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19328 eq20
    | exact resolve eq20 eq19328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19344 : y ≠ y ∨ x = y ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19328 eq56
    | (have r₁ := eq56
       have r₂ := eq19328
       grind)
    | exact resolve eq56 eq19328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq19408 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq19328
  have eq19409 : x = y ∨ x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq19344
  have eq19474 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19341
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19341
    | exact resolve eq19341 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19341
  have eq24567 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19409
       have r₂ := eq19408
       grind)
    | exact resolve eq19409 eq19408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19409
  have eq51143 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17841 eq17523
    | exact resolve eq17523 eq17841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17523 eq17841
  have eq51185 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq51143
  have eq51201 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq51185 eq27
    | exact resolve eq27 eq51185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51185
  have eq51212 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq51201
       have r₂ := eq19474
       grind)
    | exact resolve eq51201 eq19474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19474 eq51201
  have eq51217 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq51212 eq51
    | (have r₁ := eq51
       have r₂ := eq51212
       grind)
    | exact resolve eq51 eq51212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq51212
  have eq51221 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq51217
  have eq51238 : (τ (σ y)) = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq51221 eq55
    | exact resolve eq55 eq51221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq51221
  have eq51312 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq51238
    | exact resolve eq51238 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq51238
  have eq51318 : y = (k x y) := by
    first
    | (have r₁ := eq51312
       have r₂ := eq50
       grind)
    | exact resolve eq51312 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq51312
  have eq51329 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq51318
       grind)
    | exact superpose eq51318 eq44
    | exact resolve eq44 eq51318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq51345 : x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24567
       have i₂ := eq51318
       grind)
    | exact superpose eq51318 eq24567
    | exact resolve eq24567 eq51318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24567 eq51318
  have eq51372 : x = (M.op x y) := by
    first
    | (have r₁ := eq51345
       have r₂ := eq19408
       grind)
    | exact resolve eq51345 eq19408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19408 eq51345
  have eq51383 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq51329
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq51329
    | exact resolve eq51329 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq51329
  have eq51391 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq51372 eq20
    | exact resolve eq20 eq51372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq51372
  have eq51618 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq51391
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq51391
    | exact resolve eq51391 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq51391
  have eq51620 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq51618 eq26
    | exact resolve eq26 eq51618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq51685 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq51618 eq4468
    | exact resolve eq4468 eq51618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4468
  have eq51746 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq51685
       have r₂ := eq27
       grind)
    | exact resolve eq51685 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51685
  have eq51808 : (σ y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq51618 eq51383
    | exact resolve eq51383 eq51618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51383 eq51618
  have eq51853 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq51620 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq51620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51854 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq51620 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq51620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51620
  have eq51856 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq51854
       have r₂ := eq27
       grind)
    | exact resolve eq51854 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51854
  have eq51857 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq51853
       have r₂ := eq27
       grind)
    | exact resolve eq51853 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51853
  have eq51858 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq51808 eq51856
    | exact resolve eq51856 eq51808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51856
  have eq51859 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq51808 eq51857
    | exact resolve eq51857 eq51808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51857
  have eq59779 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq51808 eq51746
    | exact resolve eq51746 eq51808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51746 eq51808
  have eq59780 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq59779
  have eq62958 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq51859
       have r₂ := eq59780
       grind)
    | exact resolve eq51859 eq59780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51859
  have eq62960 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq62958 eq59780
    | exact resolve eq59780 eq62958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59780 eq62958
  have eq62969 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq62960
  have eq63780 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq62969 eq27
    | exact resolve eq27 eq62969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq63786 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq62969 eq51858
    | (have r₁ := eq51858
       have r₂ := eq62969
       grind)
    | exact resolve eq51858 eq62969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51858 eq62969
  have eq63787 : (σ (M.op x y)) = (σ y) := by grind
  clear eq63786
  have eq64095 : False := by grind
  exact eq64095

/-- `x □ y = if m(X,Y) = X then Y else if m(X,Y) = Y then X else if m(X,Y) = m(Y,X) then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxy_x_pxy_y_pxy_pyx_y_x_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a b = a ∨ M.op a b = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
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
  have eq50 : x ≠ (M.op x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
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
  have eq56 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ x = (k x y) := by
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
  have eq57 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq68 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
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
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq68
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq68
    | exact resolve eq68 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq74 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq72
    | exact resolve eq72 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq76 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq74
    | exact resolve eq74 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq78 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq76
    | exact resolve eq76 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq78
    | exact resolve eq78 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq86 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq3327 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq65 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq65
    | (have j0 := eq65 y
       grind)
    | exact resolve eq65 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq3342 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq3327
    | exact resolve eq3327 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3327
  have eq3358 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq3342
    | exact resolve eq3342 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3342
  have eq3362 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3358
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq3358
    | exact resolve eq3358 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3358
  have eq3363 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq3362
    | exact resolve eq3362 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3362
  have eq3364 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq3363
    | exact resolve eq3363 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3363
  have eq14720 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq79 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14721 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq14720
    | exact resolve eq14720 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14720
  have eq14732 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14721
       have r₂ := eq27
       grind)
    | exact resolve eq14721 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14721
  have eq14734 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq14732
    | exact resolve eq14732 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14732
  have eq14736 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq14734
    | exact resolve eq14734 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14734
  have eq14738 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq14736
    | exact resolve eq14736 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14736
  have eq14740 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14738 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq14738
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq14738
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq14738
       grind)
    | exact resolve eq12 eq14738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14738
  have eq14747 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14740
       have r₂ := eq26
       grind)
    | exact resolve eq14740 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14740
  have eq14749 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq14747
    | exact resolve eq14747 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14747
  have eq14750 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq14749
  have eq14751 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq14750
    | exact resolve eq14750 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14750
  have eq14752 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq14751
  have eq14782 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14752 eq79
    | exact resolve eq79 eq14752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq14752
  have eq14790 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14782
  have eq14792 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq14790
       have r₂ := eq27
       grind)
    | exact resolve eq14790 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14790
  have eq14794 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq14792
       grind)
    | exact superpose eq14792 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq14792
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq14792
       grind)
    | exact resolve eq12 eq14792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14795 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq14792
       grind)
    | exact superpose eq14792 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq14792
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq14792
       grind)
    | exact resolve eq12 eq14792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14792
  have eq14799 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14795
  have eq14800 : x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq14799
       have r₂ := eq18
       grind)
    | exact resolve eq14799 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14799
  have eq14801 : y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq14794
       have r₂ := eq18
       grind)
    | exact resolve eq14794 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14794
  have eq14802 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14800
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14800
    | exact resolve eq14800 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14800
  have eq14803 : y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14801
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14801
    | exact resolve eq14801 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14801
  have eq14804 : y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14803
  have eq14805 : x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14804
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14804
    | exact resolve eq14804 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14804
  have eq14806 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14805
  have eq14808 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq86
       have i₂ := eq14802
       grind)
    | exact superpose eq14802 eq86
    | exact resolve eq86 eq14802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq14802
  have eq14826 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq14808
    | exact resolve eq14808 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14808
  have eq14828 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq14806
       grind)
    | exact superpose eq14806 eq44
    | exact resolve eq44 eq14806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14806
  have eq14846 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq14828
    | exact resolve eq14828 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14828
  have eq15041 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14846 eq3364
    | exact resolve eq3364 eq14846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14846
  have eq15045 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq15041
  have eq15049 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq15045
       have r₂ := eq27
       grind)
    | exact resolve eq15045 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15045
  have eq15074 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15049 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq15049
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq15049
       grind)
    | exact resolve eq12 eq15049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15049
  have eq15078 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq15074
  have eq15079 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq15078
       have r₂ := eq26
       grind)
    | exact resolve eq15078 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15078
  have eq15081 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq15079
    | exact resolve eq15079 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15079
  have eq15097 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15081 eq14826
    | exact resolve eq14826 eq15081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14826 eq15081
  have eq15099 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15097
  have eq15101 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq15099
       have r₂ := eq27
       grind)
    | exact resolve eq15099 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15099
  have eq15340 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15101 eq57
    | (have r₁ := eq57
       have r₂ := eq15101
       grind)
    | exact resolve eq57 eq15101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq15343 : (σ x) ≠ (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15101
  have eq15344 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15340
  have eq15820 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq15344
       have r₂ := eq15343
       grind)
    | exact resolve eq15344 eq15343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15343 eq15344
  have eq15828 : (τ (σ x)) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15820 eq55
    | exact resolve eq55 eq15820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15820
  have eq15858 : x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq15828
    | exact resolve eq15828 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq15828
  have eq15864 : x = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq15858
       have r₂ := eq56
       grind)
    | exact resolve eq15858 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15858
  have eq15868 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq15864
       grind)
    | exact superpose eq15864 eq44
    | exact resolve eq44 eq15864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15878 : x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq15864
       grind)
    | exact superpose eq15864 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq15864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15879 : x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15878
  have eq15883 : x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15879
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15879
    | exact resolve eq15879 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15879
  have eq15884 : x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15883
  have eq15893 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15868
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15868
    | exact resolve eq15868 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15868
  have eq15896 : y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15884
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15884
    | exact resolve eq15884 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15884
  have eq15898 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15896
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15896
    | exact resolve eq15896 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15896
  have eq16152 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15893 eq3364
    | exact resolve eq3364 eq15893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16159 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16152
  have eq16183 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq15898
       grind)
    | exact superpose eq15898 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq15898
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq15898
       grind)
    | exact resolve eq12 eq15898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15898
  have eq16190 : y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq16183
       have r₂ := eq18
       grind)
    | exact resolve eq16183 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16183
  have eq16192 : y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16190
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16190
    | exact resolve eq16190 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16190
  have eq16193 : y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16192
  have eq16194 : x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16193
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16193
    | exact resolve eq16193 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16193
  have eq16195 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16194
  have eq16433 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16159 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq16159
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq16159
       grind)
    | exact resolve eq12 eq16159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16159
  have eq16440 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq16433
       have r₂ := eq26
       grind)
    | exact resolve eq16433 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16433
  have eq16442 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq16440
    | exact resolve eq16440 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16440
  have eq16443 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16442
  have eq16444 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq16443
    | exact resolve eq16443 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16443
  have eq16445 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16444
  have eq16714 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15864
       have i₂ := eq16195
       grind)
    | exact superpose eq16195 eq15864
    | exact resolve eq15864 eq16195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15864 eq16195
  have eq16716 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq16714
  have eq16965 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16716 eq51
    | (have r₁ := eq51
       have r₂ := eq16716
       grind)
    | exact resolve eq51 eq16716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16716
  have eq16967 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq16965
  have eq17215 : (τ (σ y)) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16967 eq55
    | exact resolve eq55 eq16967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16967
  have eq17250 : y = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq17215
    | exact resolve eq17215 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17215
  have eq17255 : y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq17250
       have r₂ := eq50
       grind)
    | exact resolve eq17250 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17250
  have eq17275 : y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq17255
       grind)
    | exact superpose eq17255 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq17255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17276 : y = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq17275
  have eq17282 : y = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17276
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17276
    | exact resolve eq17276 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17276
  have eq17283 : y = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq17282
  have eq17295 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17283
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17283
    | exact resolve eq17283 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17283
  have eq17297 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17295
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17295
    | exact resolve eq17295 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17295
  have eq17586 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq17297
       grind)
    | exact superpose eq17297 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq17297
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq17297
       grind)
    | exact resolve eq12 eq17297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17297
  have eq17593 : y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq17586
       have r₂ := eq18
       grind)
    | exact resolve eq17586 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17586
  have eq17595 : y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17593
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17593
    | exact resolve eq17593 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17593
  have eq17596 : y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) := by grind
  clear eq17595
  have eq17597 : x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17596
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17596
    | exact resolve eq17596 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq17596
  have eq17598 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq17597
  have eq17869 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17255
       have i₂ := eq17598
       grind)
    | exact superpose eq17598 eq17255
    | exact resolve eq17255 eq17598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17255 eq17598
  have eq17871 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq17869
  have eq17884 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17871 eq20
    | exact resolve eq20 eq17871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17887 : y ≠ y ∨ x = y ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17871 eq56
    | (have r₁ := eq56
       have r₂ := eq17871
       grind)
    | exact resolve eq56 eq17871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq17951 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq17871
  have eq17952 : x = y ∨ x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq17887
  have eq18017 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17884
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17884
    | exact resolve eq17884 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17884
  have eq22749 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17952
       have r₂ := eq17951
       grind)
    | exact resolve eq17952 eq17951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17952
  have eq49610 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16445 eq15893
    | exact resolve eq15893 eq16445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15893 eq16445
  have eq49652 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq49610
  have eq49668 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq49652 eq27
    | exact resolve eq27 eq49652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49652
  have eq49679 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq49668
       have r₂ := eq18017
       grind)
    | exact resolve eq49668 eq18017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18017 eq49668
  have eq49967 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq49679 eq51
    | (have r₁ := eq51
       have r₂ := eq49679
       grind)
    | exact resolve eq51 eq49679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq49679
  have eq49971 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq49967
  have eq49988 : (τ (σ y)) = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq49971 eq55
    | exact resolve eq55 eq49971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq49971
  have eq50062 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq49988
    | exact resolve eq49988 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq49988
  have eq50068 : y = (k x y) := by
    first
    | (have r₁ := eq50062
       have r₂ := eq50
       grind)
    | exact resolve eq50062 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq50062
  have eq50356 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq50068
       grind)
    | exact superpose eq50068 eq44
    | exact resolve eq44 eq50068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq50373 : x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22749
       have i₂ := eq50068
       grind)
    | exact superpose eq50068 eq22749
    | exact resolve eq22749 eq50068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22749 eq50068
  have eq50400 : x = (M.op x y) := by
    first
    | (have r₁ := eq50373
       have r₂ := eq17951
       grind)
    | exact resolve eq50373 eq17951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17951 eq50373
  have eq50413 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq50356
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq50356
    | exact resolve eq50356 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq50356
  have eq50422 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq50400 eq20
    | exact resolve eq20 eq50400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq50400
  have eq50651 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq50422
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq50422
    | exact resolve eq50422 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq50422
  have eq50998 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq50651 eq26
    | exact resolve eq26 eq50651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq51063 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq50651 eq3364
    | exact resolve eq3364 eq50651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3364
  have eq51128 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq51063
       have r₂ := eq27
       grind)
    | exact resolve eq51063 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51063
  have eq51189 : (σ y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq50651 eq50413
    | exact resolve eq50413 eq50651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50413 eq50651
  have eq51692 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq50998 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq50998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51694 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq51692
       have r₂ := eq27
       grind)
    | exact resolve eq51692 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51692
  have eq51695 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq51189 eq51694
    | exact resolve eq51694 eq51189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51694
  have eq62016 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq51189 eq51128
    | exact resolve eq51128 eq51189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51128
  have eq62017 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq62016
  have eq62019 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq62017 eq12
    | (have j0 := eq12 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq12 eq62017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62017
  have eq62026 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq62019
       have r₂ := eq50998
       grind)
    | exact resolve eq62019 eq50998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62019
  have eq62028 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq50998 eq62026
    | exact resolve eq62026 eq50998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62026
  have eq62029 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by grind
  clear eq62028
  have eq62031 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq50998 eq62029
    | exact resolve eq62029 eq50998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50998 eq62029
  have eq62032 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq62031
       have r₂ := eq27
       grind)
    | exact resolve eq62031 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62031
  have eq62033 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq51189 eq62032
    | exact resolve eq62032 eq51189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51189 eq62032
  have eq62034 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq62033
  have eq62040 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq62034 eq27
    | exact resolve eq27 eq62034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq62046 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq62034 eq51695
    | (have r₁ := eq51695
       have r₂ := eq62034
       grind)
    | exact resolve eq51695 eq62034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51695 eq62034
  have eq62047 : (σ (M.op x y)) = (σ y) := by grind
  clear eq62046
  have eq62852 : False := by grind
  exact eq62852

/-- `x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = Y then m(Y,X) else if m(X,Y) = Y then X
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxy_x_pyx_y_pxy_y_pyx_pyx_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a b = a ∨ M.op b a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear ht hu hv hw hd nh hi1 hi2
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
  have eq42 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq35 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq35
    | exact resolve eq35 eq15
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
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
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
  have eq61 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq71 : x ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq61 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq61
    | (have j0 := eq61 y x
       grind)
    | exact resolve eq61 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq61
    | (have j0 := eq61 (σ y) (σ x)
       grind)
    | exact resolve eq61 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq68
       grind)
    | exact superpose eq68 eq16
    | exact resolve eq16 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : y ≠ (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = (k x y) := by
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
  have eq79 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq93 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq99
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq99
    | exact resolve eq99 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq112
    | exact resolve eq112 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq117 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq115
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq115
    | exact resolve eq115 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq117
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq117
    | exact resolve eq117 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq146 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
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
  clear eq39
  have eq186 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq395 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq272 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq272
    | exact resolve eq272 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq411 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq272 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq272
    | (have j0 := eq272 X0 y
       grind)
    | exact resolve eq272 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq609 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq91 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq91 X1 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq91 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq91 X0 X0
       grind)
    | exact resolve eq12 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq613 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq616 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq609 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq619 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq616 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq616 X1 X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq616 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq616 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | exact resolve eq616 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq629 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq619 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq619
    | (have j0 := eq619 X0 X1
       grind)
    | exact resolve eq619 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq630 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq629 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq3511 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq146 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq146
    | (have j0 := eq146 x
       grind)
    | exact resolve eq146 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq3520 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3511
  have eq3526 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3520
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq3520
    | exact resolve eq3520 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3520
  have eq3545 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq14 (σ x) (σ x)
       grind)
    | (have r₁ := eq3526
       have r₂ := eq14 (σ x) (σ x)
       grind)
    | exact resolve eq3526 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3526
  have eq3672 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 y)) ∨ (k (σ X0) (σ y)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq186 eq14
    | (have j0 := eq14 (σ X0) (σ y)
       have j1 := eq186 X0
       grind)
    | (have r₁ := eq14 (σ y) (σ X0)
       have r₂ := eq186 X0
       grind)
    | (have r₁ := eq14 (σ y) (σ y)
       have r₂ := eq186 y
       grind)
    | (have r₁ := eq14 (σ X0) (σ y)
       have r₂ := eq186 X0
       grind)
    | exact resolve eq14 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3674 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 y)) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq186 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq3677 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 y)) ∨ (k (σ X0) (σ y)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq3672 X0
       have j1 := eq14 (σ X0) (σ y)
       grind)
    | (have r₁ := eq3672 X0
       have r₂ := eq14 (σ y) (σ X0)
       grind)
    | (have r₁ := eq3672 y
       have r₂ := eq14 (σ y) (σ y)
       grind)
    | (have r₁ := eq3672 X0
       have r₂ := eq14 (σ X0) (σ y)
       grind)
    | exact resolve eq3672 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3672
  have eq3704 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 y)) ∨ (k (σ X0) (σ y)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq3677 X0
       have j1 := eq61 (σ X0) (σ y)
       grind)
    | (have r₁ := eq3677 X0
       have r₂ := eq61 (σ X0) (σ y)
       grind)
    | (have r₁ := eq3677 y
       have r₂ := eq61 (σ y) (σ y)
       grind)
    | exact resolve eq3677 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3677
  have eq3719 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 y)) ∨ (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq40 eq3704
    | (have j0 := eq3704 X0
       grind)
    | exact resolve eq3704 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq3704
  have eq4276 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (σ (k y X0)) ∨ (σ y) = (k (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | exact superpose eq93 eq12
    | (have j0 := eq12 (σ y) (σ X0)
       have j1 := eq93 X0
       grind)
    | (have r₁ := eq12 (σ y) (σ y)
       have r₂ := eq93 y
       grind)
    | (have r₁ := eq12 (σ y) (σ X0)
       have r₂ := eq93 X0
       grind)
    | exact resolve eq12 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4278 : ∀ X0 : G, (σ y) ≠ (σ (k y X0)) ∨ (k (σ y) (σ X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | exact superpose eq93 eq14
    | (have j0 := eq14 (σ y) (σ X0)
       have j1 := eq93 X0
       grind)
    | (have r₁ := eq14 (σ X0) (σ y)
       have r₂ := eq93 X0
       grind)
    | (have r₁ := eq14 (σ y) (σ y)
       have r₂ := eq93 y
       grind)
    | (have r₁ := eq14 (σ y) (σ X0)
       have r₂ := eq93 X0
       grind)
    | exact resolve eq14 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq4281 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (σ (k y X0)) ∨ (σ y) = (k (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4276 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4276
  have eq4283 : ∀ X0 : G, (σ y) ≠ (σ (k y X0)) ∨ (k (σ y) (σ X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4278 X0
       have j1 := eq14 (σ y) (σ X0)
       grind)
    | (have r₁ := eq4278 X0
       have r₂ := eq14 (σ X0) (σ y)
       grind)
    | (have r₁ := eq4278 y
       have r₂ := eq14 (σ y) (σ y)
       grind)
    | (have r₁ := eq4278 X0
       have r₂ := eq14 (σ y) (σ X0)
       grind)
    | exact resolve eq4278 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4278
  have eq4285 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (σ (k y X0)) ∨ (σ y) = (k (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4281 X0
       have j1 := eq12 (σ y) (σ X0)
       grind)
    | (have r₁ := eq4281 y
       have r₂ := eq12 (σ y) (σ y)
       grind)
    | (have r₁ := eq4281 X0
       have r₂ := eq12 (σ y) (σ X0)
       grind)
    | exact resolve eq4281 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4281
  have eq4322 : ∀ X0 : G, (σ y) ≠ (σ (k y X0)) ∨ (k (σ y) (σ X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4283 X0
       have j1 := eq61 (σ y) (σ X0)
       grind)
    | (have r₁ := eq4283 X0
       have r₂ := eq61 (σ y) (σ X0)
       grind)
    | (have r₁ := eq4283 y
       have r₂ := eq61 (σ y) (σ y)
       grind)
    | exact resolve eq4283 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4283
  have eq4323 : ∀ X0 : G, (σ y) = (σ (k y X0)) ∨ (σ X0) ≠ (σ (k y X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (σ (k y X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq4285
    | (have j0 := eq4285 X0
       grind)
    | exact resolve eq4285 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4285
  have eq4324 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ y) = (σ (k y X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4323 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4323
  have eq4350 : ∀ X0 : G, (σ y) ≠ (σ (k y X0)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq4322
    | (have j0 := eq4322 X0
       grind)
    | exact resolve eq4322 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq4322
  have eq5296 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq630 (τ X1) (τ X0)
       have i₂ := eq395 X0 X1
       grind)
    | exact superpose eq395 eq630
    | (have j0 := eq630 (τ X0) (τ X1)
       grind)
    | exact resolve eq630 eq395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq5474 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5296 X0 X1
       have i₂ := eq15 (k X0 X1)
       grind)
    | exact superpose eq15 eq5296
    | (have j0 := eq5296 X0 X1
       grind)
    | exact resolve eq5296 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5296
  have eq5558 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5474 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq5474
    | (have j0 := eq5474 X0 X1
       grind)
    | exact resolve eq5474 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5474
  have eq5642 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5558 X0 X1
       have i₂ := eq15 (k X0 X1)
       grind)
    | exact superpose eq15 eq5558
    | (have j0 := eq5558 X0 X1
       grind)
    | exact resolve eq5558 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5558
  have eq5724 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5642 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5642
    | (have j0 := eq5642 X0 X1
       grind)
    | exact resolve eq5642 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5642
  have eq5806 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5724 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5724
    | (have j0 := eq5724 X0 X1
       grind)
    | exact resolve eq5724 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5724
  have eq5888 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5806 X0 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5806
    | (have j0 := eq5806 X0 X1
       grind)
    | exact resolve eq5806 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5806
  have eq5915 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5888 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq5888
    | (have j0 := eq5888 X0 X1
       grind)
    | exact resolve eq5888 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5888
  have eq5940 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5915 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5915
    | (have j0 := eq5915 X0 X1
       grind)
    | exact resolve eq5915 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5915
  have eq22047 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq118 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22048 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq22047
    | exact resolve eq22047 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22047
  have eq22059 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq22048
       have r₂ := eq27
       grind)
    | exact resolve eq22048 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22048
  have eq22063 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq22059
    | exact resolve eq22059 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22059
  have eq22065 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq22063
    | exact resolve eq22063 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22063
  have eq22067 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq22065 eq61
    | (have r₁ := eq61 (σ x) (σ y)
       have r₂ := eq22065
       grind)
    | (have r₁ := eq61 (σ y) (σ x)
       have r₂ := eq22065
       grind)
    | (have r₁ := eq61 y x
       have r₂ := eq22065
       grind)
    | exact resolve eq61 eq22065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22065
  have eq22070 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq22067
  have eq22147 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq22070 eq55
    | exact resolve eq55 eq22070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22070
  have eq22177 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq22147
    | exact resolve eq22147 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq22147
  have eq24796 : y = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq22177
       grind)
    | exact superpose eq22177 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq22177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22177
  have eq24797 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq24796
  have eq24801 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24797
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24797
    | exact resolve eq24797 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24797
  have eq24802 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq24801
  have eq24818 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24802
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24802
    | exact resolve eq24802 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24802
  have eq24819 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24818
  have eq25134 : y ≠ y ∨ y = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq61 x y
       have i₂ := eq24819
       grind)
    | exact superpose eq24819 eq61
    | (have r₁ := eq61 x y
       have r₂ := eq24819
       grind)
    | (have r₁ := eq61 y x
       have r₂ := eq24819
       grind)
    | (have r₁ := eq61 (σ y) (σ x)
       have r₂ := eq24819
       grind)
    | exact resolve eq61 eq24819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25135 : y ≠ y ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq24819
       grind)
    | exact superpose eq24819 eq14
    | (have j0 := eq14 y x
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq24819
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq24819
       grind)
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq24819
       grind)
    | exact resolve eq14 eq24819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24819
  have eq25136 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq25135
  have eq25137 : y = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq25134
  have eq25138 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25136
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25136
    | exact resolve eq25136 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25136
  have eq25139 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq25138
       have r₂ := eq71
       grind)
    | exact resolve eq25138 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25138
  have eq25143 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq68
       have i₂ := eq25139
       grind)
    | exact superpose eq25139 eq68
    | exact resolve eq68 eq25139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25139
  have eq25180 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq25143
    | exact resolve eq25143 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25143
  have eq25589 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq613 x y
       have i₂ := eq25137
       grind)
    | exact superpose eq25137 eq613
    | (have j0 := eq613 x y
       grind)
    | exact resolve eq613 eq25137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613 eq25137
  have eq25595 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq25589
  have eq25599 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25595
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25595
    | exact resolve eq25595 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25595
  have eq25612 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25599
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25599
    | exact resolve eq25599 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25599
  have eq25618 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25612
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25612
    | exact resolve eq25612 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25612
  have eq25622 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25618
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25618
    | exact resolve eq25618 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25618
  have eq25626 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq25622
    | exact resolve eq25622 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25622
  have eq25627 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq25626
  have eq25631 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25627
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25627
    | exact resolve eq25627 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25627
  have eq25637 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25631
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25631
    | exact resolve eq25631 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25631
  have eq25640 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq25637
    | exact resolve eq25637 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25637
  have eq25641 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq25640
  have eq25999 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25641 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq25641
       grind)
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq25641
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq25641
       grind)
    | exact resolve eq14 eq25641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25641
  have eq26000 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq25999
  have eq26002 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq26000
    | exact resolve eq26000 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26000
  have eq26003 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq26002
       have r₂ := eq72
       grind)
    | exact resolve eq26002 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26002
  have eq26023 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26003 eq25180
    | exact resolve eq25180 eq26003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25180 eq26003
  have eq26030 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq26023
  have eq26041 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq26030
       have r₂ := eq27
       grind)
    | exact resolve eq26030 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26030
  have eq26344 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26041 eq79
    | (have r₁ := eq79
       have r₂ := eq26041
       grind)
    | exact resolve eq79 eq26041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq26347 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26041 eq27
    | exact resolve eq27 eq26041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26348 : (σ x) ≠ (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq26041
  have eq26349 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq26344
  have eq66949 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq26349
       have r₂ := eq26348
       grind)
    | exact resolve eq26349 eq26348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26349
  have eq66952 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq66949 eq61
    | (have r₁ := eq61 (σ x) (σ y)
       have r₂ := eq66949
       grind)
    | (have r₁ := eq61 (σ y) (σ x)
       have r₂ := eq66949
       grind)
    | (have r₁ := eq61 y x
       have r₂ := eq66949
       grind)
    | exact resolve eq61 eq66949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66949
  have eq66955 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq66952
  have eq67255 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq66955 eq118
    | exact resolve eq118 eq66955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66955
  have eq67278 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq67255
  have eq67287 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq67278
       have r₂ := eq26347
       grind)
    | exact resolve eq67278 eq26347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26347 eq67278
  have eq84662 : (τ (σ x)) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq67287 eq55
    | exact resolve eq55 eq67287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67287
  have eq84716 : x = (k x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq84662
    | exact resolve eq84662 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84662
  have eq84725 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq84716
       have r₂ := eq78
       grind)
    | exact resolve eq84716 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq84716
  have eq84727 : y ≠ y ∨ y = (k x y) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq61 x y
       have i₂ := eq84725
       grind)
    | exact superpose eq84725 eq61
    | (have r₁ := eq61 x y
       have r₂ := eq84725
       grind)
    | (have r₁ := eq61 y x
       have r₂ := eq84725
       grind)
    | (have r₁ := eq61 (σ y) (σ x)
       have r₂ := eq84725
       grind)
    | exact resolve eq61 eq84725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84728 : y ≠ y ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq84725
       grind)
    | exact superpose eq84725 eq14
    | (have j0 := eq14 y x
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq84725
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq84725
       grind)
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq84725
       grind)
    | exact resolve eq14 eq84725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84725
  have eq84729 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq84728
  have eq84730 : y = (k x y) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq84727
  have eq84731 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq84729
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq84729
    | exact resolve eq84729 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84729
  have eq84732 : (M.op x y) = (k y x) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq84731
       have r₂ := eq71
       grind)
    | exact resolve eq84731 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84731
  have eq85132 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq68
       have i₂ := eq84732
       grind)
    | exact superpose eq84732 eq68
    | exact resolve eq68 eq84732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84732
  have eq85219 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq85132
    | exact resolve eq85132 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85132
  have eq85377 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq84730
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq84730
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq84730 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85393 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq630 x y
       have i₂ := eq84730
       grind)
    | exact superpose eq84730 eq630
    | (have j0 := eq630 x y
       grind)
    | exact resolve eq630 eq84730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84730
  have eq85398 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq85393
  have eq85400 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq85377
  have eq85402 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq85398
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq85398
    | exact resolve eq85398 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85398
  have eq85418 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq85400
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq85400
    | exact resolve eq85400 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85400
  have eq85420 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq85402
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq85402
    | exact resolve eq85402 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85402
  have eq85425 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq85418
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq85418
    | exact resolve eq85418 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85418
  have eq85426 : y = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq85425
  have eq85428 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq85420
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq85420
    | exact resolve eq85420 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85420
  have eq85432 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq85428
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq85428
    | exact resolve eq85428 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85428
  have eq85436 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq85432
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq85432
    | exact resolve eq85432 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85432
  have eq85440 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq85436
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq85436
    | exact resolve eq85436 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85436
  have eq85444 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq85440
    | exact resolve eq85440 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85440
  have eq85445 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (k x y) := by grind
  clear eq85444
  have eq85846 : y ≠ y ∨ y = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq61 x y
       have i₂ := eq85426
       grind)
    | exact superpose eq85426 eq61
    | (have r₁ := eq61 x y
       have r₂ := eq85426
       grind)
    | (have r₁ := eq61 (σ y) (σ x)
       have r₂ := eq85426
       grind)
    | (have r₁ := eq61 y x
       have r₂ := eq85426
       grind)
    | exact resolve eq61 eq85426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85847 : y ≠ y ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq85426
       grind)
    | exact superpose eq85426 eq14
    | (have j0 := eq14 y x
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq85426
       grind)
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq85426
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq85426
       grind)
    | exact resolve eq14 eq85426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85426
  have eq85848 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq85847
  have eq85849 : y = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq85846
  have eq85850 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq85848
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq85848
    | exact resolve eq85848 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85848
  have eq85851 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq85850
       have r₂ := eq71
       grind)
    | exact resolve eq85850 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85850
  have eq85859 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq68
       have i₂ := eq85851
       grind)
    | exact superpose eq85851 eq68
    | exact resolve eq68 eq85851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85851
  have eq85980 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq85859
    | exact resolve eq85859 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85859
  have eq86602 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq630 x y
       have i₂ := eq85849
       grind)
    | exact superpose eq85849 eq630
    | (have j0 := eq630 x y
       grind)
    | exact resolve eq630 eq85849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630 eq85849
  have eq86606 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq86602
  have eq86610 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq86606
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq86606
    | exact resolve eq86606 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86606
  have eq86627 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq86610
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq86610
    | exact resolve eq86610 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86610
  have eq86632 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq86627
       have r₂ := eq26348
       grind)
    | exact resolve eq86627 eq26348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26348 eq86627
  have eq86634 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq86632
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq86632
    | exact resolve eq86632 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86632
  have eq86636 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq86634
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq86634
    | exact resolve eq86634 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86634
  have eq86638 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq86636
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq86636
    | exact resolve eq86636 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86636
  have eq86639 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq86638
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq86638
    | exact resolve eq86638 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86638
  have eq86640 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq86639
    | exact resolve eq86639 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86639
  have eq86641 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq86640
  have eq87097 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq86641 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq86641
       grind)
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq86641
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq86641
       grind)
    | exact resolve eq14 eq86641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86641
  have eq87098 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq87097
  have eq87101 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq87098
    | exact resolve eq87098 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87098
  have eq87102 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq87101
       have r₂ := eq72
       grind)
    | exact resolve eq87101 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87101
  have eq87112 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq87102 eq77
    | exact resolve eq77 eq87102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87184 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq87102 eq85980
    | exact resolve eq85980 eq87102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85980 eq87102
  have eq87191 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq87184
  have eq87259 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq87191
       have r₂ := eq27
       grind)
    | exact resolve eq87191 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87191
  have eq87665 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq87259 eq51
    | (have r₁ := eq51
       have r₂ := eq87259
       grind)
    | exact resolve eq51 eq87259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq87666 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq87259 eq72
    | (have r₁ := eq72
       have r₂ := eq87259
       grind)
    | exact resolve eq72 eq87259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87721 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq87666
  have eq87722 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq87665
  have eq88162 : (τ (σ x)) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq87721 eq77
    | exact resolve eq77 eq87721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87721
  have eq88404 : x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq88162
    | exact resolve eq88162 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88162
  have eq88521 : x = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq88404
       grind)
    | exact superpose eq88404 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq88404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88522 : x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq88521
  have eq88614 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq88522
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq88522
    | exact resolve eq88522 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88522
  have eq88615 : y = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq88614
  have eq88743 : x = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq88404
       have i₂ := eq87112
       grind)
    | exact superpose eq87112 eq88404
    | exact resolve eq88404 eq87112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87112
  have eq88749 : x = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq88743
  have eq89301 : ∀ X0 : G, (σ (k x X0)) = (k (M.op (σ x) (σ y)) (σ X0)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq88749 eq34
    | exact resolve eq34 eq88749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89302 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq88749 eq38
    | exact resolve eq38 eq88749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq89303 : (σ (k x x)) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq88749 eq42
    | exact resolve eq42 eq88749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89336 : (k x y) = (τ (k (M.op (σ x) (σ y)) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq88749 eq411
    | exact resolve eq411 eq88749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411 eq88749
  have eq89475 : (k (σ x) (σ x)) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq89303
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq89303
    | exact resolve eq89303 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq89303
  have eq89477 : (M.op (σ x) (σ x)) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3545 eq89475
    | exact resolve eq89475 eq3545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3545 eq89475
  have eq89489 : (k x y) = (τ (M.op (σ y) (σ x))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq87722 eq55
    | exact resolve eq55 eq87722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq89490 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq87722 eq118
    | exact resolve eq118 eq87722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq87722
  have eq89519 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq89490
  have eq107905 : ∀ X0 : G, (σ (k x (τ X0))) = (k (M.op (σ x) (σ y)) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq89301 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq89301
    | exact resolve eq89301 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89301
  have eq108331 : ∀ X0 : G, (k (σ x) X0) = (k (M.op (σ x) (σ y)) X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq107905 X0
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq107905
    | exact resolve eq107905 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq107905
  have eq110219 : ∀ X0 : G, (σ (k (τ X0) x)) = (k X0 (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq89302 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq89302
    | exact resolve eq89302 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89302
  have eq110634 : ∀ X0 : G, (k X0 (σ x)) = (k X0 (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq110219 X0
       have i₂ := eq34 X0 x
       grind)
    | exact superpose eq34 eq110219
    | exact resolve eq110219 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq110219
  have eq110667 : ∀ X0 : G, (k X0 (σ x)) = (k X0 (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq110634 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq110634
    | (have j0 := eq110634 X0
       grind)
    | exact resolve eq110634 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110634
  have eq110756 : (k (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq110667 eq108331
    | exact resolve eq108331 eq110667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108331 eq110667
  have eq110850 : (k (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq110756
  have eq111067 : (k (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq110850 eq11
    | (have j0 := eq11 (M.op (σ x) (σ y)) (σ x)
       grind)
    | exact resolve eq11 eq110850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111082 : (k (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq14 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq111067
       have r₂ := eq14 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq111067
       have r₂ := eq14 (M.op (σ x) (σ y)) (σ x)
       grind)
    | (have r₁ := eq111067
       have r₂ := eq14 x y
       grind)
    | exact resolve eq111067 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111067
  have eq111084 : (k (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq61 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq111082
       have r₂ := eq61 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq111082
       have r₂ := eq61 y x
       grind)
    | exact resolve eq111082 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111082
  have eq138764 : (τ (σ (M.op x y))) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq89519 eq89489
    | exact resolve eq89489 eq89519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89489 eq89519
  have eq138768 : (τ (σ (M.op x y))) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq138764
  have eq138783 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30 eq138768
    | exact resolve eq138768 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138768
  have eq141743 : y ≠ y ∨ (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq88615
       grind)
    | exact superpose eq88615 eq14
    | (have j0 := eq14 y x
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq88615
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq88615
       grind)
    | exact resolve eq14 eq88615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88615
  have eq141745 : (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq141743
  have eq141747 : (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq141745
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq141745
    | exact resolve eq141745 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141745
  have eq141748 : (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq141747
       have r₂ := eq71
       grind)
    | exact resolve eq141747 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141747
  have eq142677 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq88404
       have i₂ := eq141748
       grind)
    | exact superpose eq141748 eq88404
    | exact resolve eq88404 eq141748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141748
  have eq142688 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq142677
  have eq142831 : x ≠ x ∨ x = (M.op x y) ∨ x = y ∨ y = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq142688
       grind)
    | exact superpose eq142688 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq142688
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq142688
       grind)
    | exact resolve eq12 eq142688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142832 : x ≠ y ∨ x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq61 x y
       have i₂ := eq142688
       grind)
    | exact superpose eq142688 eq61
    | (have r₁ := eq61 y x
       have r₂ := eq142688
       grind)
    | exact resolve eq61 eq142688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142688
  have eq142834 : x = (M.op x y) ∨ x = y ∨ y = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq142831
  have eq142847 : x = (M.op x y) ∨ x = y ∨ y = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq142834
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq142834
    | exact resolve eq142834 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142834
  have eq142848 : y = (k y x) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq142847
  have eq144239 : x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq88404
       have i₂ := eq142848
       grind)
    | exact superpose eq142848 eq88404
    | exact resolve eq88404 eq142848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144253 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq144239
  have eq144416 : (σ y) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq144253 eq20
    | exact resolve eq20 eq144253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144253
  have eq144700 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq144416
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq144416
    | exact resolve eq144416 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144416
  have eq932973 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq111084 eq89477
    | exact resolve eq89477 eq111084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89477 eq111084
  have eq933072 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by grind
  clear eq932973
  have eq946957 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by grind
  clear eq933072
  have eq1079555 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq85445 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq14 (σ y) (σ x)
       have r₂ := eq85445
       grind)
    | (have r₁ := eq14 (σ x) (σ y)
       have r₂ := eq85445
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq85445
       grind)
    | exact resolve eq14 eq85445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85445
  have eq1079558 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (k x y) := by grind
  clear eq1079555
  have eq1079575 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq26 eq1079558
    | exact resolve eq1079558 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079558
  have eq1079579 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (k x y) := by
    first
    | (have r₁ := eq1079575
       have r₂ := eq72
       grind)
    | exact resolve eq1079575 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079575
  have eq1079599 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq1079579 eq77
    | exact resolve eq77 eq1079579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1079695 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq1079579 eq85219
    | exact resolve eq85219 eq1079579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85219 eq1079579
  have eq1080001 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1079695
  have eq1080036 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1080001
       have r₂ := eq27
       grind)
    | exact resolve eq1080001 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080001
  have eq1080128 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3674 x
       have i₂ := eq1080036
       grind)
    | exact superpose eq1080036 eq3674
    | (have j0 := eq3674 x
       grind)
    | exact resolve eq3674 eq1080036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3674
  have eq1080129 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3719 x
       have i₂ := eq1080036
       grind)
    | exact superpose eq1080036 eq3719
    | (have j0 := eq3719 x
       grind)
    | exact resolve eq3719 eq1080036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3719 eq1080036
  have eq1080159 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1080129
  have eq1080160 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1080128
  have eq1080206 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1080159
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1080159
    | exact resolve eq1080159 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080159
  have eq1080207 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1080160
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1080160
    | exact resolve eq1080160 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080160
  have eq1080293 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1080206
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1080206
    | exact resolve eq1080206 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080206
  have eq1080294 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1080207
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1080207
    | exact resolve eq1080207 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080207
  have eq1080326 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1080293
    | exact resolve eq1080293 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080293
  have eq1080327 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1080294
    | exact resolve eq1080294 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080294
  have eq1080341 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1080327
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1080327
    | exact resolve eq1080327 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080327
  have eq1080349 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1080341
    | exact resolve eq1080341 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080341
  have eq1080350 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1080349
  have eq1093338 : y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1079599
       have i₂ := eq142848
       grind)
    | exact superpose eq142848 eq1079599
    | exact resolve eq1079599 eq142848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142848 eq1079599
  have eq1093746 : y = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq1093338
  have eq1093867 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1093746
       have r₂ := eq142832
       grind)
    | exact resolve eq1093746 eq142832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142832 eq1093746
  have eq1094832 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1080350 eq1080326
    | exact resolve eq1080326 eq1080350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080326 eq1080350
  have eq1094837 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1094832
  have eq1094859 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1094837 eq27
    | exact resolve eq27 eq1094837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094837
  have eq1096419 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq144700 eq1094859
    | (have r₁ := eq1094859
       have r₂ := eq144700
       grind)
    | exact resolve eq1094859 eq144700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144700 eq1094859
  have eq1096420 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1096419
  have eq1096421 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1096420
  have eq1096428 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1096421 eq72
    | (have r₁ := eq72
       have r₂ := eq1096421
       grind)
    | exact resolve eq72 eq1096421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq1096421
  have eq1097331 : (σ x) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1096428
  have eq1098299 : (τ (σ x)) = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1097331 eq77
    | exact resolve eq77 eq1097331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq1097331
  have eq1098885 : x = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq1098299
    | exact resolve eq1098299 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098299
  have eq1139947 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq138783
       have i₂ := eq1093867
       grind)
    | exact superpose eq1093867 eq138783
    | exact resolve eq138783 eq1093867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093867
  have eq1140008 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq1139947
  have eq1140215 : y ≠ y ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq1140008
       grind)
    | exact superpose eq1140008 eq14
    | (have j0 := eq14 y x
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq1140008
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq1140008
       grind)
    | exact resolve eq14 eq1140008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140008
  have eq1140218 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq1140215
  have eq1140221 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1140218
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1140218
    | exact resolve eq1140218 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140218
  have eq1140222 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq1140221
       have r₂ := eq71
       grind)
    | exact resolve eq1140221 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140221
  have eq1140358 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq88404
       have i₂ := eq1140222
       grind)
    | exact superpose eq1140222 eq88404
    | exact resolve eq88404 eq1140222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140222
  have eq1140582 : y = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1140358
  have eq1141065 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1140582 eq15
    | exact resolve eq15 eq1140582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140582
  have eq1141693 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1141065
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1141065
    | exact resolve eq1141065 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1141065
  have eq1141760 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1141693 eq87259
    | exact resolve eq87259 eq1141693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141693
  have eq1142865 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1141760
  have eq1143521 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1142865 eq26
    | exact resolve eq26 eq1142865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1143885 : (k x y) = (τ (k (M.op (σ x) (σ y)) (σ x))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1142865 eq89336
    | exact resolve eq89336 eq1142865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89336 eq1142865
  have eq1145284 : (k x y) = (τ (k (M.op (σ x) (σ y)) (σ x))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1143885
  have eq1145921 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1143521 eq946957
    | exact resolve eq946957 eq1143521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946957 eq1143521
  have eq1145935 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by grind
  clear eq1145921
  have eq1145942 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1145935
       have r₂ := eq87259
       grind)
    | exact resolve eq1145935 eq87259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145935
  have eq1146284 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1145942 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq1145942
       grind)
    | exact resolve eq14 eq1145942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1146285 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1145942 eq61
    | (have j0 := eq61 (σ y) (σ x)
       grind)
    | (have r₁ := eq61 y x
       have r₂ := eq1145942
       grind)
    | exact resolve eq61 eq1145942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145942
  have eq1146296 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1146285
       have r₂ := eq87259
       grind)
    | exact resolve eq1146285 eq87259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146285
  have eq1146297 : (k (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1146284
       have r₂ := eq87259
       grind)
    | exact resolve eq1146284 eq87259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87259 eq1146284
  have eq1152657 : (k (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1146297 eq110850
    | exact resolve eq110850 eq1146297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110850 eq1146297
  have eq1152784 : (k (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1152657
  have eq1156902 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1152784 eq1146296
    | exact resolve eq1146296 eq1152784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146296 eq1152784
  have eq1156958 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1156902
  have eq1157059 : (σ x) ≠ (σ x) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1156958 eq61
    | (have r₁ := eq61 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq1156958
       grind)
    | (have r₁ := eq61 y x
       have r₂ := eq1156958
       grind)
    | exact resolve eq61 eq1156958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq1156958
  have eq1157060 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1157059
  have eq1164435 : (τ (σ x)) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1157060 eq1145284
    | exact resolve eq1145284 eq1157060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145284 eq1157060
  have eq1164954 : (τ (σ x)) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1164435
  have eq1164985 : x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq1164954
    | exact resolve eq1164954 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1164954
  have eq1165086 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq138783
       have i₂ := eq1164985
       grind)
    | exact superpose eq1164985 eq138783
    | exact resolve eq138783 eq1164985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138783 eq1164985
  have eq1165149 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1165086
  have eq1165378 : y ≠ y ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq1165149
       grind)
    | exact superpose eq1165149 eq14
    | (have j0 := eq14 y x
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq1165149
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq1165149
       grind)
    | exact resolve eq14 eq1165149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1165149
  have eq1165381 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1165378
  have eq1165384 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1165381
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1165381
    | exact resolve eq1165381 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1165381
  have eq1165385 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1165384
       have r₂ := eq71
       grind)
    | exact resolve eq1165384 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1165384
  have eq1165522 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq88404
       have i₂ := eq1165385
       grind)
    | exact superpose eq1165385 eq88404
    | exact resolve eq88404 eq1165385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88404 eq1165385
  have eq1165746 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1165522
  have eq1166818 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq1165746
  have eq2075599 : x ≠ x ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5940 y x
       have i₂ := eq1098885
       grind)
    | exact superpose eq1098885 eq5940
    | (have j0 := eq5940 y x
       grind)
    | (have r₁ := eq5940 y x
       have r₂ := eq1098885
       grind)
    | exact resolve eq5940 eq1098885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5940
  have eq2076500 : x ≠ x ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq2075599
  have eq2076501 : x = (M.op x y) ∨ x = y ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq2076500
  have eq2076784 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2076501
       have r₂ := eq1166818
       grind)
    | exact resolve eq2076501 eq1166818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2076501
  have eq2077055 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2076784
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2076784
    | exact resolve eq2076784 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2076784
  have eq2077056 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq2077055
  have eq2077078 : y ≠ y ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq2077056
       grind)
    | exact superpose eq2077056 eq14
    | (have j0 := eq14 y x
       grind)
    | (have r₁ := eq14 y x
       have r₂ := eq2077056
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq2077056
       grind)
    | exact resolve eq14 eq2077056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2077056
  have eq2077081 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq2077078
  have eq2077084 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2077081
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2077081
    | exact resolve eq2077081 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2077081
  have eq2077085 : (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq2077084
       have r₂ := eq71
       grind)
    | exact resolve eq2077084 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2077084
  have eq2077339 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1098885
       have i₂ := eq2077085
       grind)
    | exact superpose eq2077085 eq1098885
    | exact resolve eq1098885 eq2077085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098885 eq2077085
  have eq2077415 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq2077339
  have eq2077476 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2077415
       have r₂ := eq1166818
       grind)
    | exact resolve eq2077415 eq1166818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1166818 eq2077415
  have eq2077680 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2077476 eq28
    | exact resolve eq28 eq2077476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2077476
  have eq2080114 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq2077680
    | exact resolve eq2077680 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2077680
  have eq2080115 : x = (M.op x y) := by grind
  clear eq2080114
  have eq2080267 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2080115 eq20
    | exact resolve eq20 eq2080115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2080273 : x ≠ x ∨ x = (k y x) := by
    first
    | exact superpose eq2080115 eq71
    | (have r₁ := eq71
       have r₂ := eq2080115
       grind)
    | exact resolve eq71 eq2080115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq2080115
  have eq2080901 : x = (k y x) := by grind
  clear eq2080273
  have eq2081465 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2080267
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2080267
    | exact resolve eq2080267 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2080267
  have eq2081646 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2081465 eq26
    | exact resolve eq26 eq2081465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2083665 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq68
       have i₂ := eq2080901
       grind)
    | exact superpose eq2080901 eq68
    | exact resolve eq68 eq2080901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq2084015 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq4324 x
       have i₂ := eq2080901
       grind)
    | exact superpose eq2080901 eq4324
    | (have j0 := eq4324 x
       grind)
    | exact resolve eq4324 eq2080901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4324
  have eq2084016 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq4350 x
       have i₂ := eq2080901
       grind)
    | exact superpose eq2080901 eq4350
    | (have j0 := eq4350 x
       grind)
    | exact resolve eq4350 eq2080901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4350 eq2080901
  have eq2084044 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq2084015
  have eq2084067 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq2084016
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2084016
    | exact resolve eq2084016 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2084016
  have eq2084068 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq2084044
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2084044
    | exact resolve eq2084044 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2084044
  have eq2084186 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq2081465 eq2083665
    | exact resolve eq2083665 eq2081465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2083665
  have eq2084201 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq2081465 eq2084067
    | exact resolve eq2084067 eq2081465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2084067
  have eq2084202 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq2081465 eq2084068
    | exact resolve eq2084068 eq2081465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2084068
  have eq2084296 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2084186
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2084186
    | exact resolve eq2084186 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2084186
  have eq2084310 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq2084201
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2084201
    | exact resolve eq2084201 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2084201
  have eq2084311 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq2084202
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2084202
    | exact resolve eq2084202 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2084202
  have eq2084405 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq2081465 eq2084296
    | exact resolve eq2084296 eq2081465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2084296
  have eq2084417 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq2084310
    | exact resolve eq2084310 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2084310
  have eq2084418 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq2084311
    | exact resolve eq2084311 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2084311
  have eq2084485 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq2081465 eq2084417
    | exact resolve eq2084417 eq2081465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2084417
  have eq2084486 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq2081465 eq2084418
    | exact resolve eq2084418 eq2081465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2084418
  have eq2084517 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq2084485
       have r₂ := eq27
       grind)
    | exact resolve eq2084485 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2084485
  have eq2084518 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq2084486
       have r₂ := eq27
       grind)
    | exact resolve eq2084486 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2084486
  have eq2084539 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq2084517
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2084517
    | exact resolve eq2084517 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2084517
  have eq2084540 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2084518
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2084518
    | exact resolve eq2084518 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2084518
  have eq2084560 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq2081465 eq2084539
    | exact resolve eq2084539 eq2081465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2084539
  have eq2084561 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2081465 eq2084540
    | exact resolve eq2084540 eq2081465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2081465 eq2084540
  have eq2091369 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2084561 eq14
    | (have j0 := eq14 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq14 (σ y) (σ (M.op x y))
       have r₂ := eq2084561
       grind)
    | exact resolve eq14 eq2084561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2084561
  have eq2091372 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq2091369
  have eq2091374 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2081646 eq2091372
    | exact resolve eq2091372 eq2081646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2091372
  have eq2091375 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2084405 eq2091374
    | exact resolve eq2091374 eq2084405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2084405 eq2091374
  have eq2091376 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq2091375
       have r₂ := eq27
       grind)
    | exact resolve eq2091375 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2091375
  have eq2092678 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2091376 eq2081646
    | exact resolve eq2081646 eq2091376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2081646
  have eq2092680 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2091376 eq2084560
    | (have r₁ := eq2084560
       have r₂ := eq2091376
       grind)
    | exact resolve eq2084560 eq2091376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2084560 eq2091376
  have eq2092681 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq2092680
  have eq2098304 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2092678 eq2092681
    | exact resolve eq2092681 eq2092678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2092678 eq2092681
  have eq2098305 : False := by grind
  exact eq2098305
