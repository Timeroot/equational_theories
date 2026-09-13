import equational_theories.Definability.AutBox3
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then m(X,Y) else if X = Y then m(X,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_y_pyy_x_x_y_pxy_pxy_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq31 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) ∨ (M.op X1 X1) = X1 := by
    intro X1
    grind
  have eq32 : x = (τ (σ x)) := by
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
  have eq33 : y = (τ (σ y)) := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq39 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq40 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq42 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq47 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  have eq48 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq53 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq47
       grind)
    | exact superpose eq47 eq16
    | exact resolve eq16 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq31
    | (have j0 := eq31 (σ X0)
       grind)
    | exact resolve eq31 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq47
       have i₂ := eq31 x
       grind)
    | exact superpose eq31 eq47
    | (have j1 := eq31 x
       grind)
    | exact resolve eq47 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq53
       have i₂ := eq31 sF2
       grind)
    | exact superpose eq31 eq53
    | (have j1 := eq31 (σ x)
       grind)
    | exact resolve eq53 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq73 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq40
    | (have j0 := eq40 x
       grind)
    | exact resolve eq40 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq27
       grind)
    | exact superpose eq27 eq40
    | (have j0 := eq40 y
       grind)
    | exact resolve eq40 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq86 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq86
    | exact resolve eq86 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq23 eq92
    | exact resolve eq92 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq94 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq31 y
       grind)
    | exact superpose eq31 eq74
    | (have j1 := eq31 y
       grind)
    | exact resolve eq74 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq109 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq99
       have i₂ := eq31 sF3
       grind)
    | exact superpose eq31 eq99
    | (have j1 := eq31 (σ y)
       grind)
    | exact resolve eq99 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq308 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq42
  have eq388 : ∀ X0 : G, (k (σ X0) (σ (k X0 X0))) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq389 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq63 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq390 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq388 X0
       have i₂ := eq10 X0 (k X0 X0)
       grind)
    | exact superpose eq10 eq388
    | (have j0 := eq388 X0
       grind)
    | exact resolve eq388 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq2919 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq389 (τ X0)
       have i₂ := eq38 X0 (τ X0)
       grind)
    | exact superpose eq38 eq389
    | (have j0 := eq389 (τ X0)
       grind)
    | exact resolve eq389 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2926 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2919 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2919
    | (have j0 := eq2919 X0
       grind)
    | exact resolve eq2919 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2919
  have eq2932 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2926 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2926
    | (have j0 := eq2926 X0
       grind)
    | exact resolve eq2926 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2926
  have eq3168 : ∀ X0 : G, (σ (k (τ X0) (k (τ X0) (τ X0)))) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq390 (τ X0)
       have i₂ := eq38 X0 (τ X0)
       grind)
    | exact superpose eq38 eq390
    | (have j0 := eq390 (τ X0)
       grind)
    | exact resolve eq390 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq3178 : ∀ X0 : G, (σ (k (τ X0) (k (τ X0) (τ X0)))) = (M.op X0 (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3168 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3168
    | (have j0 := eq3168 X0
       grind)
    | exact resolve eq3168 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3168
  have eq3193 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k X0 (σ (k (τ X0) (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3178 X0
       have i₂ := eq38 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq38 eq3178
    | (have j0 := eq3178 X0
       grind)
    | exact resolve eq3178 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3178
  have eq3206 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k X0 (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3193 X0
       have i₂ := eq38 X0 (τ X0)
       grind)
    | exact superpose eq38 eq3193
    | (have j0 := eq3193 X0
       grind)
    | exact resolve eq3193 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq3193
  have eq3213 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3206 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3206
    | (have j0 := eq3206 X0
       grind)
    | exact resolve eq3206 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3206
  have eq3220 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3213 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3213
    | (have j0 := eq3213 X0
       grind)
    | exact resolve eq3213 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3213
  have eq5261 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq308 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq308
    | exact resolve eq308 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq5353 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (σ (k (M.op X0 X0) X0)) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq5261 X0
       have i₂ := eq10 (M.op X0 X0) X0
       grind)
    | exact superpose eq10 eq5261
    | (have j0 := eq5261 X0
       grind)
    | exact resolve eq5261 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5261
  have eq15172 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq93 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq15173 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq15172
    | exact resolve eq15172 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15172
  have eq15184 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq15173
       have r₂ := eq30
       grind)
    | exact resolve eq15173 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15173
  have eq15186 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq15184 eq66
    | exact resolve eq66 eq15184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq15184
  have eq15190 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq15186
  have eq15192 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq33 eq15190
    | exact resolve eq15190 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15190
  have eq15368 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq15192 eq109
    | exact resolve eq109 eq15192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq15192
  have eq15371 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq15368
  have eq15373 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq32 eq15371
    | exact resolve eq15371 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15371
  have eq15384 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq31 x
       have i₂ := eq15373
       grind)
    | exact superpose eq15373 eq31
    | (have j0 := eq31 x
       grind)
    | exact resolve eq31 eq15373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15392 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq15384
  have eq15418 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq65
       have i₂ := eq15392
       grind)
    | exact superpose eq15392 eq65
    | exact resolve eq65 eq15392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15420 : (M.op x y) = (k x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq15392
  have eq15423 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq15418
  have eq15424 : (M.op x y) = (k x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq15420
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq15420
    | exact resolve eq15420 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15420
  have eq15425 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq15423
       have i₂ := eq27
       grind)
    | exact superpose eq27 eq15423
    | exact resolve eq15423 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15423
  have eq15644 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq48
       have i₂ := eq15424
       grind)
    | exact superpose eq15424 eq48
    | exact resolve eq48 eq15424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15424
  have eq15664 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq23 eq15644
    | exact resolve eq15644 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15644
  have eq15684 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15425 eq3220
    | (have j0 := eq3220 (σ x)
       grind)
    | exact resolve eq3220 eq15425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3220
  have eq15685 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq15684
    | exact resolve eq15684 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15684
  have eq70684 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15685 eq15664
    | exact resolve eq15664 eq15685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15664 eq15685
  have eq70687 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq70684
  have eq70696 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq70687
       have r₂ := eq30
       grind)
    | exact resolve eq70687 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70687
  have eq70703 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  have eq70729 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq70703 eq15425
    | exact resolve eq15425 eq70703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15425 eq70703
  have eq70748 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq70729
  have eq70765 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq70748 eq70696
    | exact resolve eq70696 eq70748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70696 eq70748
  have eq70770 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq70765
  have eq70788 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq31 y
       have i₂ := eq70770
       grind)
    | exact superpose eq70770 eq31
    | (have j0 := eq31 y
       grind)
    | exact resolve eq31 eq70770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70796 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq70788
  have eq71558 : (k y y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq70796
  have eq72325 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq70770
       have i₂ := eq71558
       grind)
    | exact superpose eq71558 eq70770
    | exact resolve eq70770 eq71558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70770 eq71558
  have eq72332 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq72325
  have eq72344 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq94
       have i₂ := eq72332
       grind)
    | exact superpose eq72332 eq94
    | exact resolve eq94 eq72332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72345 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq72332
  have eq72347 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq72344
  have eq72349 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72345
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq72345
    | exact resolve eq72345 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72345
  have eq72350 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72347
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq72347
    | exact resolve eq72347 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72347
  have eq72973 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq72350
       have i₂ := eq31 sF3
       grind)
    | exact superpose eq31 eq72350
    | (have j1 := eq31 (σ y)
       grind)
    | exact resolve eq72350 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76717 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq48
       have i₂ := eq72349
       grind)
    | exact superpose eq72349 eq48
    | exact resolve eq48 eq72349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72349
  have eq76760 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq23 eq76717
    | exact resolve eq76717 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76717
  have eq76766 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq72973
  have eq104957 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq76766 eq72350
    | exact resolve eq72350 eq76766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72350 eq76766
  have eq105008 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq104957
  have eq105736 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq105008
  have eq105740 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq105736
    | exact resolve eq105736 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105736
  have eq106141 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq105740 eq76760
    | exact resolve eq76760 eq105740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106144 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq106141
  have eq106155 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq106144
       have r₂ := eq30
       grind)
    | exact resolve eq106144 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106144
  have eq106161 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq106155
  have eq106165 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq29 eq106161
    | exact resolve eq106161 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106161
  have eq106187 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq106165 eq76760
    | exact resolve eq76760 eq106165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76760 eq106165
  have eq106190 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq106187
  have eq106201 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq106190
       have r₂ := eq30
       grind)
    | exact resolve eq106190 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106190
  have eq106207 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq106201
  have eq106212 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq106207
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq106207
    | exact resolve eq106207 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106207
  have eq107094 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq48
       have i₂ := eq106212
       grind)
    | exact superpose eq106212 eq48
    | exact resolve eq48 eq106212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106212
  have eq107137 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq23 eq107094
    | exact resolve eq107094 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107094
  have eq108073 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq107137 eq105740
    | exact resolve eq105740 eq107137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105740
  have eq108078 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq108073
  have eq108096 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq108078
       have r₂ := eq30
       grind)
    | exact resolve eq108078 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108078
  have eq108165 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq108096
  have eq108169 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq108165
    | exact resolve eq108165 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108165
  have eq108928 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq108169 eq107137
    | exact resolve eq107137 eq108169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107137 eq108169
  have eq108931 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq108928
  have eq108944 : x = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq108931
       have r₂ := eq30
       grind)
    | exact resolve eq108931 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108931
  have eq108949 : (k x x) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  have eq109658 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq47
       have i₂ := eq108949
       grind)
    | exact superpose eq108949 eq47
    | exact resolve eq47 eq108949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq109671 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq15373
       have i₂ := eq108949
       grind)
    | exact superpose eq108949 eq15373
    | exact resolve eq15373 eq108949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15373 eq108949
  have eq109708 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq109671
  have eq109722 : (σ x) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq109658
       have i₂ := eq108944
       grind)
    | exact superpose eq108944 eq109658
    | exact resolve eq109658 eq108944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109658
  have eq109845 : (σ x) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq109722
  have eq109851 : (σ x) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq109845
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq109845
    | exact resolve eq109845 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109845
  have eq109889 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq109851 eq2932
    | (have j0 := eq2932 (σ x)
       grind)
    | (have r₁ := eq2932 (σ x)
       have r₂ := eq109851
       grind)
    | exact resolve eq2932 eq109851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2932 eq109851
  have eq109894 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq109889
  have eq2132509 : x = y ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq108944
       have i₂ := eq109708
       grind)
    | exact superpose eq109708 eq108944
    | exact resolve eq108944 eq109708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109708
  have eq2133851 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq2132509
  have eq2136497 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq31 y
       have i₂ := eq2133851
       grind)
    | exact superpose eq2133851 eq31
    | (have j0 := eq31 y
       grind)
    | exact resolve eq31 eq2133851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2136510 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2136497
  have eq2136632 : (k y y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2136510
  have eq2140981 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2133851
       have i₂ := eq2136632
       grind)
    | exact superpose eq2136632 eq2133851
    | exact resolve eq2133851 eq2136632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2133851 eq2136632
  have eq2140992 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2140981
  have eq2141047 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq94
       have i₂ := eq2140992
       grind)
    | exact superpose eq2140992 eq94
    | exact resolve eq94 eq2140992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq2141057 : (σ (M.op x y)) = (σ (k x y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5353 y
       have i₂ := eq2140992
       grind)
    | exact superpose eq2140992 eq5353
    | exact resolve eq5353 eq2140992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5353 eq2140992
  have eq2141070 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2141047
  have eq2141075 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2141057
       have i₂ := eq48
       grind)
    | exact superpose eq48 eq2141057
    | exact resolve eq2141057 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq2141057
  have eq2141083 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2141070
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2141070
    | exact resolve eq2141070 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2141070
  have eq2141085 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2141075
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq2141075
    | exact resolve eq2141075 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2141075
  have eq2141089 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq23 eq2141085
    | exact resolve eq2141085 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2141085
  have eq2143211 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq2141083
       have i₂ := eq31 sF3
       grind)
    | exact superpose eq31 eq2141083
    | (have j1 := eq31 (σ y)
       grind)
    | exact resolve eq2141083 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2163508 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2143211
  have eq2322198 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq2163508 eq2141083
    | exact resolve eq2141083 eq2163508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2141083 eq2163508
  have eq2322319 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2322198
  have eq2325746 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2322319
  have eq2325757 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29 eq2325746
    | exact resolve eq2325746 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2325746
  have eq2330274 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2325757 eq2141089
    | exact resolve eq2141089 eq2325757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2141089 eq2325757
  have eq2330279 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2330274
  have eq2330296 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq2330279
       have r₂ := eq30
       grind)
    | exact resolve eq2330279 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2330279
  have eq2330307 : (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq2330296 eq109894
    | exact resolve eq109894 eq2330296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109894 eq2330296
  have eq2331583 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2330307
  have eq2335453 : x = y ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq108944
       have i₂ := eq2331583
       grind)
    | exact superpose eq2331583 eq108944
    | exact resolve eq108944 eq2331583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108944 eq2331583
  have eq2336801 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2335453
  have eq2337390 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq2336801 eq33
    | exact resolve eq33 eq2336801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq2336801
  have eq2337873 : x = y ∨ x = y := by
    first
    | exact superpose eq32 eq2337390
    | exact resolve eq2337390 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq2337390
  have eq2337874 : x = y := by grind
  clear eq2337873
  have eq2337880 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq21
       have i₂ := eq2337874
       grind)
    | exact superpose eq2337874 eq21
    | exact resolve eq21 eq2337874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq2337881 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq27
       have i₂ := eq2337874
       grind)
    | exact superpose eq2337874 eq27
    | exact resolve eq27 eq2337874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2337874
  have eq2339067 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2337881
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2337881
    | exact resolve eq2337881 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2337881
  have eq2339074 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2339067 eq29
    | exact resolve eq29 eq2339067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2339067
  have eq2339628 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq65
       have i₂ := eq2337880
       grind)
    | exact superpose eq2337880 eq65
    | exact resolve eq65 eq2337880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq2340324 : (k x (M.op x y)) = (M.op x (M.op x y)) := by grind
  have eq2340337 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23 eq2339628
    | exact resolve eq2339628 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2339628
  have eq2341009 : (k (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by grind
  have eq2341542 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2340337 eq31
    | (have j0 := eq31 (σ x)
       grind)
    | exact resolve eq31 eq2340337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq2341561 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2339074 eq2341542
    | exact resolve eq2341542 eq2339074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2341542
  have eq2341611 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2341561
       have r₂ := eq30
       grind)
    | exact resolve eq2341561 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2341561
  have eq2341636 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2339074 eq2341611
    | exact resolve eq2341611 eq2339074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2341611
  have eq2346585 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2341636 eq2341009
    | exact resolve eq2341009 eq2341636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2341009 eq2341636
  have eq2346587 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2339074 eq2346585
    | exact resolve eq2346585 eq2339074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2346585
  have eq2353327 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2346587 eq2340337
    | exact resolve eq2340337 eq2346587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2340337 eq2346587
  have eq2353341 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2353327
  have eq2353348 : x = (M.op x y) := by
    first
    | (have r₁ := eq2353341
       have r₂ := eq30
       grind)
    | exact resolve eq2353341 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2353341
  have eq2353404 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2353348 eq23
    | exact resolve eq23 eq2353348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq2354285 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq2353348 eq2340324
    | exact resolve eq2340324 eq2353348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2340324
  have eq2354288 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq2354285
       have i₂ := eq2337880
       grind)
    | exact superpose eq2337880 eq2354285
    | exact resolve eq2354285 eq2337880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2337880 eq2354285
  have eq2354870 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2353404
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2353404
    | exact resolve eq2353404 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2353404
  have eq2354872 : x = (k x x) := by
    first
    | exact superpose eq2353348 eq2354288
    | exact resolve eq2354288 eq2353348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2353348 eq2354288
  have eq2357986 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq389 x
       have i₂ := eq2354872
       grind)
    | exact superpose eq2354872 eq389
    | (have j0 := eq389 x
       grind)
    | exact resolve eq389 eq2354872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389 eq2354872
  have eq2358004 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2357986
  have eq2358021 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2358004
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2358004
    | exact resolve eq2358004 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2358004
  have eq2358112 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2339074 eq2358021
    | exact resolve eq2358021 eq2339074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2339074 eq2358021
  have eq2358198 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2354870 eq2358112
    | exact resolve eq2358112 eq2354870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2354870 eq2358112
  have eq2358282 : False := by grind
  exact eq2358282

/-- `x □ y = if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then m(X,Y) else if X = Y then m(Y,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_y_pyy_x_x_y_pxy_pxy_pyy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq31 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) ∨ (M.op X1 X1) = X1 := by
    intro X1
    grind
  have eq32 : x = (τ (σ x)) := by
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
  have eq33 : y = (τ (σ y)) := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq39 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq40 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq42 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq47 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  have eq48 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq53 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq47
       grind)
    | exact superpose eq47 eq16
    | exact resolve eq16 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq31
    | (have j0 := eq31 (σ X0)
       grind)
    | exact resolve eq31 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq47
       have i₂ := eq31 x
       grind)
    | exact superpose eq31 eq47
    | (have j1 := eq31 x
       grind)
    | exact resolve eq47 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq53
       have i₂ := eq31 sF2
       grind)
    | exact superpose eq31 eq53
    | (have j1 := eq31 (σ x)
       grind)
    | exact resolve eq53 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq73 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq40
    | (have j0 := eq40 x
       grind)
    | exact resolve eq40 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq27
       grind)
    | exact superpose eq27 eq40
    | (have j0 := eq40 y
       grind)
    | exact resolve eq40 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq86 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq86
    | exact resolve eq86 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq23 eq92
    | exact resolve eq92 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq94 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq31 y
       grind)
    | exact superpose eq31 eq74
    | (have j1 := eq31 y
       grind)
    | exact resolve eq74 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq109 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq99
       have i₂ := eq31 sF3
       grind)
    | exact superpose eq31 eq99
    | (have j1 := eq31 (σ y)
       grind)
    | exact resolve eq99 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq308 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq42
  have eq388 : ∀ X0 : G, (k (σ X0) (σ (k X0 X0))) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq389 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq63 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq390 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq388 X0
       have i₂ := eq10 X0 (k X0 X0)
       grind)
    | exact superpose eq10 eq388
    | (have j0 := eq388 X0
       grind)
    | exact resolve eq388 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq2919 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq389 (τ X0)
       have i₂ := eq38 X0 (τ X0)
       grind)
    | exact superpose eq38 eq389
    | (have j0 := eq389 (τ X0)
       grind)
    | exact resolve eq389 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2926 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2919 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2919
    | (have j0 := eq2919 X0
       grind)
    | exact resolve eq2919 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2919
  have eq2932 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2926 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2926
    | (have j0 := eq2926 X0
       grind)
    | exact resolve eq2926 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2926
  have eq3168 : ∀ X0 : G, (σ (k (τ X0) (k (τ X0) (τ X0)))) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq390 (τ X0)
       have i₂ := eq38 X0 (τ X0)
       grind)
    | exact superpose eq38 eq390
    | (have j0 := eq390 (τ X0)
       grind)
    | exact resolve eq390 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq3178 : ∀ X0 : G, (σ (k (τ X0) (k (τ X0) (τ X0)))) = (M.op X0 (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3168 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3168
    | (have j0 := eq3168 X0
       grind)
    | exact resolve eq3168 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3168
  have eq3193 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k X0 (σ (k (τ X0) (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3178 X0
       have i₂ := eq38 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq38 eq3178
    | (have j0 := eq3178 X0
       grind)
    | exact resolve eq3178 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3178
  have eq3206 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k X0 (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3193 X0
       have i₂ := eq38 X0 (τ X0)
       grind)
    | exact superpose eq38 eq3193
    | (have j0 := eq3193 X0
       grind)
    | exact resolve eq3193 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq3193
  have eq3213 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3206 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3206
    | (have j0 := eq3206 X0
       grind)
    | exact resolve eq3206 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3206
  have eq3220 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3213 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3213
    | (have j0 := eq3213 X0
       grind)
    | exact resolve eq3213 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3213
  have eq5261 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq308 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq308
    | exact resolve eq308 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq5353 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (σ (k (M.op X0 X0) X0)) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq5261 X0
       have i₂ := eq10 (M.op X0 X0) X0
       grind)
    | exact superpose eq10 eq5261
    | (have j0 := eq5261 X0
       grind)
    | exact resolve eq5261 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5261
  have eq15172 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq93 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq15173 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq15172
    | exact resolve eq15172 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15172
  have eq15184 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq15173
       have r₂ := eq30
       grind)
    | exact resolve eq15173 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15173
  have eq15186 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq15184 eq66
    | exact resolve eq66 eq15184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq15184
  have eq15190 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq15186
  have eq15192 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq33 eq15190
    | exact resolve eq15190 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15190
  have eq15368 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq15192 eq109
    | exact resolve eq109 eq15192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq15192
  have eq15371 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq15368
  have eq15373 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq32 eq15371
    | exact resolve eq15371 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15371
  have eq15384 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq31 x
       have i₂ := eq15373
       grind)
    | exact superpose eq15373 eq31
    | (have j0 := eq31 x
       grind)
    | exact resolve eq31 eq15373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15392 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq15384
  have eq15418 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq65
       have i₂ := eq15392
       grind)
    | exact superpose eq15392 eq65
    | exact resolve eq65 eq15392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15420 : (M.op x y) = (k x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq15392
  have eq15423 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq15418
  have eq15424 : (M.op x y) = (k x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq15420
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq15420
    | exact resolve eq15420 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15420
  have eq15425 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq15423
       have i₂ := eq27
       grind)
    | exact superpose eq27 eq15423
    | exact resolve eq15423 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15423
  have eq15644 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq48
       have i₂ := eq15424
       grind)
    | exact superpose eq15424 eq48
    | exact resolve eq48 eq15424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15424
  have eq15664 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq23 eq15644
    | exact resolve eq15644 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15644
  have eq15684 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15425 eq3220
    | (have j0 := eq3220 (σ x)
       grind)
    | exact resolve eq3220 eq15425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3220
  have eq15685 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq15684
    | exact resolve eq15684 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15684
  have eq70684 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15685 eq15664
    | exact resolve eq15664 eq15685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15664 eq15685
  have eq70687 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq70684
  have eq70696 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq70687
       have r₂ := eq30
       grind)
    | exact resolve eq70687 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70687
  have eq70703 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  have eq70729 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq70703 eq15425
    | exact resolve eq15425 eq70703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15425 eq70703
  have eq70748 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq70729
  have eq70765 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq70748 eq70696
    | exact resolve eq70696 eq70748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70696 eq70748
  have eq70770 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq70765
  have eq70788 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq31 y
       have i₂ := eq70770
       grind)
    | exact superpose eq70770 eq31
    | (have j0 := eq31 y
       grind)
    | exact resolve eq31 eq70770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70796 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq70788
  have eq71558 : (k y y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq70796
  have eq72325 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq70770
       have i₂ := eq71558
       grind)
    | exact superpose eq71558 eq70770
    | exact resolve eq70770 eq71558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70770 eq71558
  have eq72332 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq72325
  have eq72344 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq94
       have i₂ := eq72332
       grind)
    | exact superpose eq72332 eq94
    | exact resolve eq94 eq72332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72345 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq72332
  have eq72347 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq72344
  have eq72349 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72345
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq72345
    | exact resolve eq72345 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72345
  have eq72350 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72347
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq72347
    | exact resolve eq72347 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72347
  have eq72973 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq72350
       have i₂ := eq31 sF3
       grind)
    | exact superpose eq31 eq72350
    | (have j1 := eq31 (σ y)
       grind)
    | exact resolve eq72350 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76717 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq48
       have i₂ := eq72349
       grind)
    | exact superpose eq72349 eq48
    | exact resolve eq48 eq72349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72349
  have eq76760 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq23 eq76717
    | exact resolve eq76717 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76717
  have eq76766 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq72973
  have eq104957 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq76766 eq72350
    | exact resolve eq72350 eq76766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72350 eq76766
  have eq105008 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq104957
  have eq105736 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq105008
  have eq105740 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq105736
    | exact resolve eq105736 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105736
  have eq106141 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq105740 eq76760
    | exact resolve eq76760 eq105740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106144 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq106141
  have eq106155 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq106144
       have r₂ := eq30
       grind)
    | exact resolve eq106144 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106144
  have eq106161 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq106155
  have eq106165 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq29 eq106161
    | exact resolve eq106161 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106161
  have eq106187 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq106165 eq76760
    | exact resolve eq76760 eq106165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76760 eq106165
  have eq106190 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq106187
  have eq106201 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq106190
       have r₂ := eq30
       grind)
    | exact resolve eq106190 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106190
  have eq106207 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq106201
  have eq106212 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq106207
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq106207
    | exact resolve eq106207 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106207
  have eq107094 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq48
       have i₂ := eq106212
       grind)
    | exact superpose eq106212 eq48
    | exact resolve eq48 eq106212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106212
  have eq107137 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq23 eq107094
    | exact resolve eq107094 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107094
  have eq108073 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq107137 eq105740
    | exact resolve eq105740 eq107137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105740
  have eq108078 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq108073
  have eq108096 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq108078
       have r₂ := eq30
       grind)
    | exact resolve eq108078 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108078
  have eq108165 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq108096
  have eq108169 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq108165
    | exact resolve eq108165 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108165
  have eq108928 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq108169 eq107137
    | exact resolve eq107137 eq108169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107137 eq108169
  have eq108931 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq108928
  have eq108944 : x = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq108931
       have r₂ := eq30
       grind)
    | exact resolve eq108931 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108931
  have eq108949 : (k x x) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  have eq109658 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq47
       have i₂ := eq108949
       grind)
    | exact superpose eq108949 eq47
    | exact resolve eq47 eq108949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq109671 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ y = (M.op x x) ∨ x = y ∨ x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq15373
       have i₂ := eq108949
       grind)
    | exact superpose eq108949 eq15373
    | exact resolve eq15373 eq108949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15373 eq108949
  have eq109708 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq109671
  have eq109722 : (σ x) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq109658
       have i₂ := eq108944
       grind)
    | exact superpose eq108944 eq109658
    | exact resolve eq109658 eq108944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109658
  have eq109845 : (σ x) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq109722
  have eq109851 : (σ x) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq109845
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq109845
    | exact resolve eq109845 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109845
  have eq109889 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq109851 eq2932
    | (have j0 := eq2932 (σ x)
       grind)
    | (have r₁ := eq2932 (σ x)
       have r₂ := eq109851
       grind)
    | exact resolve eq2932 eq109851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2932 eq109851
  have eq109894 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq109889
  have eq2132509 : x = y ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq108944
       have i₂ := eq109708
       grind)
    | exact superpose eq109708 eq108944
    | exact resolve eq108944 eq109708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109708
  have eq2133851 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq2132509
  have eq2136497 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq31 y
       have i₂ := eq2133851
       grind)
    | exact superpose eq2133851 eq31
    | (have j0 := eq31 y
       grind)
    | exact resolve eq31 eq2133851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2136510 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2136497
  have eq2136632 : (k y y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2136510
  have eq2140981 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2133851
       have i₂ := eq2136632
       grind)
    | exact superpose eq2136632 eq2133851
    | exact resolve eq2133851 eq2136632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2133851 eq2136632
  have eq2140992 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2140981
  have eq2141047 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq94
       have i₂ := eq2140992
       grind)
    | exact superpose eq2140992 eq94
    | exact resolve eq94 eq2140992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq2141057 : (σ (M.op x y)) = (σ (k x y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5353 y
       have i₂ := eq2140992
       grind)
    | exact superpose eq2140992 eq5353
    | exact resolve eq5353 eq2140992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5353 eq2140992
  have eq2141070 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2141047
  have eq2141075 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2141057
       have i₂ := eq48
       grind)
    | exact superpose eq48 eq2141057
    | exact resolve eq2141057 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq2141057
  have eq2141083 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2141070
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2141070
    | exact resolve eq2141070 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2141070
  have eq2141085 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2141075
       have i₂ := eq21
       grind)
    | exact superpose eq21 eq2141075
    | exact resolve eq2141075 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2141075
  have eq2141089 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq23 eq2141085
    | exact resolve eq2141085 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2141085
  have eq2143211 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq2141083
       have i₂ := eq31 sF3
       grind)
    | exact superpose eq31 eq2141083
    | (have j1 := eq31 (σ y)
       grind)
    | exact resolve eq2141083 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2163508 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2143211
  have eq2322198 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq2163508 eq2141083
    | exact resolve eq2141083 eq2163508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2141083 eq2163508
  have eq2322319 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2322198
  have eq2325746 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2322319
  have eq2325757 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29 eq2325746
    | exact resolve eq2325746 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2325746
  have eq2330274 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2325757 eq2141089
    | exact resolve eq2141089 eq2325757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2141089 eq2325757
  have eq2330279 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2330274
  have eq2330296 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq2330279
       have r₂ := eq30
       grind)
    | exact resolve eq2330279 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2330279
  have eq2330307 : (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq2330296 eq109894
    | exact resolve eq109894 eq2330296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109894 eq2330296
  have eq2331583 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2330307
  have eq2335453 : x = y ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq108944
       have i₂ := eq2331583
       grind)
    | exact superpose eq2331583 eq108944
    | exact resolve eq108944 eq2331583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108944 eq2331583
  have eq2336801 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2335453
  have eq2337390 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq2336801 eq33
    | exact resolve eq33 eq2336801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq2336801
  have eq2337873 : x = y ∨ x = y := by
    first
    | exact superpose eq32 eq2337390
    | exact resolve eq2337390 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq2337390
  have eq2337874 : x = y := by grind
  clear eq2337873
  have eq2337880 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq21
       have i₂ := eq2337874
       grind)
    | exact superpose eq2337874 eq21
    | exact resolve eq21 eq2337874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq2337881 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq27
       have i₂ := eq2337874
       grind)
    | exact superpose eq2337874 eq27
    | exact resolve eq27 eq2337874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2337874
  have eq2339067 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2337881
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2337881
    | exact resolve eq2337881 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2337881
  have eq2339074 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2339067 eq29
    | exact resolve eq29 eq2339067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2339067
  have eq2339628 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq65
       have i₂ := eq2337880
       grind)
    | exact superpose eq2337880 eq65
    | exact resolve eq65 eq2337880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq2340324 : (k x (M.op x y)) = (M.op x (M.op x y)) := by grind
  have eq2340337 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23 eq2339628
    | exact resolve eq2339628 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2339628
  have eq2341009 : (k (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by grind
  have eq2341542 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2340337 eq31
    | (have j0 := eq31 (σ x)
       grind)
    | exact resolve eq31 eq2340337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq2341561 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2339074 eq2341542
    | exact resolve eq2341542 eq2339074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2341542
  have eq2341611 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2341561
       have r₂ := eq30
       grind)
    | exact resolve eq2341561 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2341561
  have eq2341636 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2339074 eq2341611
    | exact resolve eq2341611 eq2339074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2341611
  have eq2346585 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2341636 eq2341009
    | exact resolve eq2341009 eq2341636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2341009 eq2341636
  have eq2346587 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2339074 eq2346585
    | exact resolve eq2346585 eq2339074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2346585
  have eq2353327 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2346587 eq2340337
    | exact resolve eq2340337 eq2346587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2340337 eq2346587
  have eq2353341 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2353327
  have eq2353348 : x = (M.op x y) := by
    first
    | (have r₁ := eq2353341
       have r₂ := eq30
       grind)
    | exact resolve eq2353341 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2353341
  have eq2353404 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2353348 eq23
    | exact resolve eq23 eq2353348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq2354285 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq2353348 eq2340324
    | exact resolve eq2340324 eq2353348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2340324
  have eq2354288 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq2354285
       have i₂ := eq2337880
       grind)
    | exact superpose eq2337880 eq2354285
    | exact resolve eq2354285 eq2337880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2337880 eq2354285
  have eq2354870 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2353404
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2353404
    | exact resolve eq2353404 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2353404
  have eq2354872 : x = (k x x) := by
    first
    | exact superpose eq2353348 eq2354288
    | exact resolve eq2354288 eq2353348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2353348 eq2354288
  have eq2357986 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq389 x
       have i₂ := eq2354872
       grind)
    | exact superpose eq2354872 eq389
    | (have j0 := eq389 x
       grind)
    | exact resolve eq389 eq2354872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389 eq2354872
  have eq2358004 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2357986
  have eq2358021 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2358004
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2358004
    | exact resolve eq2358004 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2358004
  have eq2358112 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2339074 eq2358021
    | exact resolve eq2358021 eq2339074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2339074 eq2358021
  have eq2358198 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2354870 eq2358112
    | exact resolve eq2358112 eq2354870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2354870 eq2358112
  have eq2358282 : False := by grind
  exact eq2358282

/-- `x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X) else if X = Y then m(X,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_y_pyy_x_x_y_pyx_pyx_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq20 : ∀ X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq21 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26
    | exact resolve eq26 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq20
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq67 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq71 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq68 (σ X0)
       grind)
    | exact superpose eq68 eq15
    | exact resolve eq15 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq68 (τ X0)
       grind)
    | exact superpose eq68 eq35
    | exact resolve eq35 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq80 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq73
    | exact resolve eq73 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq82 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq71
    | exact resolve eq71 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq71
  have eq98 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq99 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq98 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq98
    | exact resolve eq98 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq102 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    grind
  clear eq99
  have eq688 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq696 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = X1 ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq21
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq21 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq705 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ (M.op X0 X0)) = X1 ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq696 X0 X1
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq696
    | (have j0 := eq696 X0 X1
       grind)
    | exact resolve eq696 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq696
  have eq713 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq688 X0 X1
       have i₂ := eq82 X1
       grind)
    | exact superpose eq82 eq688
    | (have j0 := eq688 X0 X1
       grind)
    | exact resolve eq688 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq727 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq713 X0 X1
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq713
    | (have j0 := eq713 X0 X1
       grind)
    | exact resolve eq713 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq734 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq740 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq734 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq750 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq740 (σ X0)
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq740
    | exact resolve eq740 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq771 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq750 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq750
    | exact resolve eq750 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq781 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq771 X0
       have i₂ := eq740 X0
       grind)
    | exact superpose eq740 eq771
    | exact resolve eq771 eq740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740 eq771
  have eq887 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq727 x y
       grind)
    | exact superpose eq727 eq16
    | (have j1 := eq727 x y
       grind)
    | exact resolve eq16 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq10365 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq705 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq705
    | (have j0 := eq705 (σ X0) X1
       grind)
    | exact resolve eq705 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq10498 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10365 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10365
    | (have j0 := eq10365 X0 X1
       grind)
    | exact resolve eq10365 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10365
  have eq10511 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10498 X0 X1
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq10498
    | (have j0 := eq10498 X0 X1
       grind)
    | exact resolve eq10498 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10498
  have eq10519 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10511 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq10511
    | (have j0 := eq10511 X0 X1
       grind)
    | exact resolve eq10511 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10511
  have eq16851 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq887
       have i₂ := eq10519 x y
       grind)
    | exact superpose eq10519 eq887
    | (have j1 := eq10519 x y
       grind)
    | (have r₁ := eq887
       have r₂ := eq10519 x y
       grind)
    | (have r₁ := eq887
       have r₂ := eq10519 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq887
       have r₂ := eq10519 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq887 eq10519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887 eq10519
  have eq16852 : x = y ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq16851
  have eq1773971 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16852
       grind)
    | exact superpose eq16852 eq16
    | exact resolve eq16 eq16852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16852
  have eq1773990 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1773971
       have r₂ := eq82 x
       grind)
    | exact resolve eq1773971 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1773971
  have eq1774068 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq781 x
       have i₂ := eq1773990
       grind)
    | exact superpose eq1773990 eq781
    | exact resolve eq781 eq1773990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1773990
  have eq1774228 : x = (M.op y y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1774068
       have r₂ := eq16
       grind)
    | exact resolve eq1774068 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774068
  have eq1774301 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq102 y
       have i₂ := eq1774228
       grind)
    | exact superpose eq1774228 eq102
    | exact resolve eq102 eq1774228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774228
  have eq1774478 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1774301
       have r₂ := eq16
       grind)
    | exact resolve eq1774301 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774301
  have eq1774496 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq1774478
       grind)
    | exact superpose eq1774478 eq9
    | exact resolve eq9 eq1774478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774478
  have eq1775038 : x = y ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1774496
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq1774496
    | exact resolve eq1774496 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774496
  have eq1775041 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1775038
       grind)
    | exact superpose eq1775038 eq16
    | exact resolve eq16 eq1775038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775038
  have eq1775060 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1775041
       have r₂ := eq82 x
       grind)
    | exact resolve eq1775041 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq1775041
  have eq1775281 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq1775060
       grind)
    | exact superpose eq1775060 eq9
    | exact resolve eq9 eq1775060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775060
  have eq1775904 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1775281
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1775281
    | exact resolve eq1775281 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775281
  have eq1775996 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq781 x
       have i₂ := eq1775904
       grind)
    | exact superpose eq1775904 eq781
    | exact resolve eq781 eq1775904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781 eq1775904
  have eq1776154 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1775996
       have r₂ := eq16
       grind)
    | exact resolve eq1775996 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775996
  have eq1776385 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq1776154
       grind)
    | exact superpose eq1776154 eq9
    | exact resolve eq9 eq1776154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776154
  have eq1777008 : x = (M.op y y) := by
    first
    | (have i₁ := eq1776385
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq1776385
    | exact resolve eq1776385 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776385
  have eq1777236 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq102 y
       have i₂ := eq1777008
       grind)
    | exact superpose eq1777008 eq102
    | exact resolve eq102 eq1777008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq1777008
  have eq1777411 : False := by grind
  exact eq1777411

/-- `x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X) else if X = Y then m(Y,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_y_pyy_x_x_y_pyx_pyx_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hw hd nh hi1 hi2
  have eq20 : ∀ X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq21 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26
    | exact resolve eq26 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq20
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq67 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq71 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq68 (σ X0)
       grind)
    | exact superpose eq68 eq15
    | exact resolve eq15 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq68 (τ X0)
       grind)
    | exact superpose eq68 eq35
    | exact resolve eq35 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq80 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq73
    | exact resolve eq73 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq82 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq71
    | exact resolve eq71 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq71
  have eq98 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq99 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq98 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq98
    | exact resolve eq98 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq102 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    grind
  clear eq99
  have eq688 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq696 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = X1 ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq21
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq21 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq705 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ (M.op X0 X0)) = X1 ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq696 X0 X1
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq696
    | (have j0 := eq696 X0 X1
       grind)
    | exact resolve eq696 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq696
  have eq713 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq688 X0 X1
       have i₂ := eq82 X1
       grind)
    | exact superpose eq82 eq688
    | (have j0 := eq688 X0 X1
       grind)
    | exact resolve eq688 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq727 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq713 X0 X1
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq713
    | (have j0 := eq713 X0 X1
       grind)
    | exact resolve eq713 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq734 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq740 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq734 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq750 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq740 (σ X0)
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq740
    | exact resolve eq740 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq771 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq750 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq750
    | exact resolve eq750 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq781 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq771 X0
       have i₂ := eq740 X0
       grind)
    | exact superpose eq740 eq771
    | exact resolve eq771 eq740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740 eq771
  have eq887 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq727 x y
       grind)
    | exact superpose eq727 eq16
    | (have j1 := eq727 x y
       grind)
    | exact resolve eq16 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq10365 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq705 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq705
    | (have j0 := eq705 (σ X0) X1
       grind)
    | exact resolve eq705 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq10498 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10365 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10365
    | (have j0 := eq10365 X0 X1
       grind)
    | exact resolve eq10365 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10365
  have eq10511 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10498 X0 X1
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq10498
    | (have j0 := eq10498 X0 X1
       grind)
    | exact resolve eq10498 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10498
  have eq10519 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10511 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq10511
    | (have j0 := eq10511 X0 X1
       grind)
    | exact resolve eq10511 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10511
  have eq16851 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq887
       have i₂ := eq10519 x y
       grind)
    | exact superpose eq10519 eq887
    | (have j1 := eq10519 x y
       grind)
    | (have r₁ := eq887
       have r₂ := eq10519 x y
       grind)
    | (have r₁ := eq887
       have r₂ := eq10519 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq887
       have r₂ := eq10519 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq887 eq10519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887 eq10519
  have eq16852 : x = y ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq16851
  have eq1773971 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16852
       grind)
    | exact superpose eq16852 eq16
    | exact resolve eq16 eq16852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16852
  have eq1773990 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1773971
       have r₂ := eq82 x
       grind)
    | exact resolve eq1773971 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1773971
  have eq1774068 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq781 x
       have i₂ := eq1773990
       grind)
    | exact superpose eq1773990 eq781
    | exact resolve eq781 eq1773990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1773990
  have eq1774228 : x = (M.op y y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1774068
       have r₂ := eq16
       grind)
    | exact resolve eq1774068 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774068
  have eq1774301 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq102 y
       have i₂ := eq1774228
       grind)
    | exact superpose eq1774228 eq102
    | exact resolve eq102 eq1774228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774228
  have eq1774478 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1774301
       have r₂ := eq16
       grind)
    | exact resolve eq1774301 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774301
  have eq1774496 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9 y
       have i₂ := eq1774478
       grind)
    | exact superpose eq1774478 eq9
    | exact resolve eq9 eq1774478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774478
  have eq1775038 : x = y ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1774496
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq1774496
    | exact resolve eq1774496 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1774496
  have eq1775041 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1775038
       grind)
    | exact superpose eq1775038 eq16
    | exact resolve eq16 eq1775038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775038
  have eq1775060 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1775041
       have r₂ := eq82 x
       grind)
    | exact resolve eq1775041 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq1775041
  have eq1775281 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq1775060
       grind)
    | exact superpose eq1775060 eq9
    | exact resolve eq9 eq1775060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775060
  have eq1775904 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1775281
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1775281
    | exact resolve eq1775281 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775281
  have eq1775996 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq781 x
       have i₂ := eq1775904
       grind)
    | exact superpose eq1775904 eq781
    | exact resolve eq781 eq1775904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781 eq1775904
  have eq1776154 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1775996
       have r₂ := eq16
       grind)
    | exact resolve eq1775996 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775996
  have eq1776385 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq9 (M.op y y)
       have i₂ := eq1776154
       grind)
    | exact superpose eq1776154 eq9
    | exact resolve eq9 eq1776154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776154
  have eq1777008 : x = (M.op y y) := by
    first
    | (have i₁ := eq1776385
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq1776385
    | exact resolve eq1776385 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776385
  have eq1777236 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq102 y
       have i₂ := eq1777008
       grind)
    | exact superpose eq1777008 eq102
    | exact resolve eq102 eq1777008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq1777008
  have eq1777411 : False := by grind
  exact eq1777411

/-- `x □ y = if m(X,X) = Y then m(X,Y) else if m(Y,Y) = Y then m(Y,X) else if m(Y,Y) = X then m(X,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_y_pyy_y_pyy_x_pxy_pyx_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq40 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq67 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq68 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq70 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq68
       grind)
    | exact superpose eq68 eq16
    | exact resolve eq16 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq70 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq70
    | (have j0 := eq70 (σ X0) (σ X1)
       grind)
    | exact resolve eq70 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq38 eq70
    | (have j0 := eq70 (σ y) (σ X0)
       grind)
    | exact resolve eq70 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq92 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq45
       have i₂ := eq70 x x
       grind)
    | exact superpose eq70 eq45
    | (have j1 := eq70 x x
       grind)
    | exact resolve eq45 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq67
       have i₂ := eq70 y x
       grind)
    | exact superpose eq70 eq67
    | (have j1 := eq70 y x
       grind)
    | exact resolve eq67 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq68
       have i₂ := eq70 y y
       grind)
    | exact superpose eq70 eq68
    | (have j1 := eq70 y y
       grind)
    | exact resolve eq68 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq51
       have i₂ := eq70 sF2 sF2
       grind)
    | exact superpose eq70 eq51
    | (have j1 := eq70 (σ x) (σ x)
       grind)
    | exact resolve eq51 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq101 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq99
  have eq102 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq95
  have eq103 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq92
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq93
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq93
    | exact resolve eq93 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq22 eq104
    | exact resolve eq104 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq109 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq80
       have i₂ := eq70 sF3 sF3
       grind)
    | exact superpose eq70 eq80
    | (have j1 := eq70 (σ y) (σ y)
       grind)
    | exact resolve eq80 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq111 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq109
  have eq307 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq40
  have eq386 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op X1 X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq86 X0 X0
       grind)
    | exact superpose eq86 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq86 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq86 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq86 X1 X1
       grind)
    | exact resolve eq13 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387 : ∀ X0 : G, (k (σ X0) (σ (k X0 X0))) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq389 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq86 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq390 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq389 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq392 : ∀ X0 : G, (k (σ X0) (σ (k X0 X0))) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq387 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq393 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op X1 X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq386 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq395 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq392 X0
       have i₂ := eq10 X0 (k X0 X0)
       grind)
    | exact superpose eq10 eq392
    | (have j0 := eq392 X0
       grind)
    | exact resolve eq392 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392
  have eq396 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op X1 X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq393 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq393 X0 (σ X0)
       have r₂ := eq13 X0 (σ X0)
       grind)
    | (have r₁ := eq393 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq393 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq3116 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq88 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq88
    | (have j0 := eq88 y
       grind)
    | exact resolve eq88 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq3118 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3116
  have eq3120 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3118
       have i₂ := eq68
       grind)
    | exact superpose eq68 eq3118
    | exact resolve eq3118 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq3118
  have eq4334 : ∀ X0 : G, (σ (k (τ X0) (k (τ X0) (τ X0)))) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq395 (τ X0)
       have i₂ := eq36 X0 (τ X0)
       grind)
    | exact superpose eq36 eq395
    | (have j0 := eq395 (τ X0)
       grind)
    | exact resolve eq395 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq4344 : ∀ X0 : G, (σ (k (τ X0) (k (τ X0) (τ X0)))) = (M.op X0 (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4334 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4334
    | (have j0 := eq4334 X0
       grind)
    | exact resolve eq4334 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4334
  have eq4362 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k X0 (σ (k (τ X0) (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4344 X0
       have i₂ := eq36 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq36 eq4344
    | (have j0 := eq4344 X0
       grind)
    | exact resolve eq4344 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4344
  have eq4375 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k X0 (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4362 X0
       have i₂ := eq36 X0 (τ X0)
       grind)
    | exact superpose eq36 eq4362
    | (have j0 := eq4362 X0
       grind)
    | exact resolve eq4362 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4362
  have eq4382 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4375 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4375
    | (have j0 := eq4375 X0
       grind)
    | exact resolve eq4375 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4375
  have eq4389 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4382 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4382
    | (have j0 := eq4382 X0
       grind)
    | exact resolve eq4382 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4382
  have eq4494 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op X1 X1) ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq396 (τ X0) X1
       have i₂ := eq36 X0 (τ X0)
       grind)
    | exact superpose eq36 eq396
    | (have j0 := eq396 (τ X0) X1
       grind)
    | exact resolve eq396 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq396
  have eq4502 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op X1 X1) ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4494 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4494
    | (have j0 := eq4494 X0 X1
       grind)
    | exact resolve eq4494 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4494
  have eq4508 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4502 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4502
    | (have j0 := eq4502 X0 X1
       grind)
    | exact resolve eq4502 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4502
  have eq4514 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4508 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4508
    | (have j0 := eq4508 X0 X1
       grind)
    | exact resolve eq4508 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4508
  have eq6235 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
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
  have eq6340 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (σ (k (M.op X0 X0) X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq6235 X0
       have i₂ := eq10 (M.op X0 X0) X0
       grind)
    | exact superpose eq10 eq6235
    | (have j0 := eq6235 X0
       grind)
    | exact resolve eq6235 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6235
  have eq13318 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq105 eq70
    | (have j0 := eq70 (σ y) (σ x)
       grind)
    | exact resolve eq70 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq13319 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq13318
    | exact resolve eq13318 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13318
  have eq13330 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq13319
       have r₂ := eq29
       grind)
    | exact resolve eq13319 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13319
  have eq13332 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq13330 eq101
    | exact resolve eq101 eq13330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq13338 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq31 eq13332
    | exact resolve eq13332 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13332
  have eq13847 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq13338 eq111
    | exact resolve eq111 eq13338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13338
  have eq13852 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq13847
  have eq13854 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq13852
    | exact resolve eq13852 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13852
  have eq13872 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq70 x x
       have i₂ := eq13854
       grind)
    | exact superpose eq13854 eq70
    | (have j0 := eq70 y x
       grind)
    | exact resolve eq70 eq13854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13854
  have eq13873 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq13872
  have eq13901 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq13873
       grind)
    | exact superpose eq13873 eq103
    | exact resolve eq103 eq13873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13904 : (M.op x y) = (k x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by grind
  have eq13905 : x ≠ y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq13873
  have eq13907 : (M.op x y) = (k x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13904
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq13904
    | exact resolve eq13904 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13904
  have eq13909 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13901
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq13901
    | exact resolve eq13901 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13901
  have eq13942 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq13907
       grind)
    | exact superpose eq13907 eq46
    | exact resolve eq46 eq13907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13907
  have eq13965 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq22 eq13942
    | exact resolve eq13942 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13942
  have eq18160 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq13909
       have r₂ := eq13905
       grind)
    | exact resolve eq13909 eq13905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13905 eq13909
  have eq18431 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18160 eq4389
    | (have j0 := eq4389 (σ x)
       grind)
    | exact resolve eq4389 eq18160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4389
  have eq18437 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq18431
    | exact resolve eq18431 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18431
  have eq119083 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18437 eq13965
    | exact resolve eq13965 eq18437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13965 eq18437
  have eq119101 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq119083
  have eq119109 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq119101
       have r₂ := eq29
       grind)
    | exact resolve eq119101 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119101
  have eq119116 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  have eq119923 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq119116 eq18160
    | exact resolve eq18160 eq119116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18160 eq119116
  have eq119943 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq119923
  have eq119959 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq119943 eq119109
    | exact resolve eq119109 eq119943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119109 eq119943
  have eq119966 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq119959
  have eq119993 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq70 y y
       have i₂ := eq119966
       grind)
    | exact superpose eq119966 eq70
    | (have j0 := eq70 y y
       grind)
    | exact resolve eq70 eq119966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119994 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq119993
  have eq120801 : (k y y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq119994
  have eq120854 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq119966
       have i₂ := eq120801
       grind)
    | exact superpose eq120801 eq119966
    | exact resolve eq119966 eq120801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119966 eq120801
  have eq120862 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq120854
  have eq120878 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq102
       have i₂ := eq120862
       grind)
    | exact superpose eq120862 eq102
    | exact resolve eq102 eq120862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120879 : (M.op x y) = (k x y) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq120862
  have eq120883 : (M.op x y) = (k x y) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq120879
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq120879
    | exact resolve eq120879 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120879
  have eq120884 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq120878
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq120878
    | exact resolve eq120878 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120878
  have eq122001 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq3120 eq120884
    | exact resolve eq120884 eq3120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130126 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq46
       have i₂ := eq120883
       grind)
    | exact superpose eq120883 eq46
    | exact resolve eq46 eq120883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120883
  have eq130201 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq22 eq130126
    | exact resolve eq130126 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130126
  have eq133942 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq122001
  have eq172554 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq133942 eq120884
    | exact resolve eq120884 eq133942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120884 eq133942
  have eq172607 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq172554
  have eq172619 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq172607
  have eq172622 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq172619
  have eq172626 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq172622
    | exact resolve eq172622 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172622
  have eq175026 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq172626 eq130201
    | exact resolve eq130201 eq172626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175031 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq175026
  have eq175042 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq175031
       have r₂ := eq29
       grind)
    | exact resolve eq175031 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175031
  have eq175050 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by grind
  clear eq175042
  have eq175056 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq28 eq175050
    | exact resolve eq175050 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175050
  have eq176056 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq175056 eq130201
    | exact resolve eq130201 eq175056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130201 eq175056
  have eq176059 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq176056
  have eq176077 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq176059
       have r₂ := eq29
       grind)
    | exact resolve eq176059 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176059
  have eq176084 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq176077
  have eq176090 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq176084
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq176084
    | exact resolve eq176084 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176084
  have eq177073 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq46
       have i₂ := eq176090
       grind)
    | exact superpose eq176090 eq46
    | exact resolve eq46 eq176090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176090
  have eq177122 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq22 eq177073
    | exact resolve eq177073 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177073
  have eq177228 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq177122 eq172626
    | exact resolve eq172626 eq177122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172626
  have eq177233 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq177228
  have eq177242 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq177233
       have r₂ := eq29
       grind)
    | exact resolve eq177233 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177233
  have eq178298 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq177242
  have eq178304 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq178298
    | exact resolve eq178298 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178298
  have eq179306 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq178304 eq177122
    | exact resolve eq177122 eq178304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177122 eq178304
  have eq179309 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq179306
  have eq179321 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq179309
       have r₂ := eq29
       grind)
    | exact resolve eq179309 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179309
  have eq179325 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = x ∨ (k X0 x) = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq179321
       grind)
    | exact superpose eq179321 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq179321
       grind)
    | exact resolve eq13 eq179321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179326 : (k x x) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  have eq179327 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (M.op X0 X0) = x ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq179325 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179325
  have eq180270 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq45
       have i₂ := eq179326
       grind)
    | exact superpose eq179326 eq45
    | exact resolve eq45 eq179326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq179326
  have eq180341 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq180270
       have i₂ := eq179321
       grind)
    | exact superpose eq179321 eq180270
    | exact resolve eq180270 eq179321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180270
  have eq180469 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq180341
  have eq180475 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq180469
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq180469
    | exact resolve eq180469 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180469
  have eq180517 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq180475 eq4514
    | (have j0 := eq4514 (σ x) X0
       grind)
    | (have r₁ := eq4514 (σ x) x
       have r₂ := eq180475
       grind)
    | exact resolve eq4514 eq180475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4514
  have eq180520 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq180475 eq70
    | (have j0 := eq70 (σ x) (σ x)
       grind)
    | exact resolve eq70 eq180475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180475
  have eq180521 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq180520
  have eq180524 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (M.op X0 X0) = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq180517 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180517
  have eq279944 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq67
       have i₂ := eq179327 y
       grind)
    | exact superpose eq179327 eq67
    | (have j1 := eq179327 y
       grind)
    | exact resolve eq67 eq179327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq179327
  have eq280786 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq279944
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq279944
    | exact resolve eq279944 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279944
  have eq280807 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22 eq280786
    | exact resolve eq280786 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280786
  have eq288772 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq180524 eq280807
    | (have j1 := eq180524 (σ y)
       grind)
    | exact resolve eq280807 eq180524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180524 eq280807
  have eq289118 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq288772
  have eq289376 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq28 eq289118
    | exact resolve eq289118 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289118
  have eq289468 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq289376
       have r₂ := eq29
       grind)
    | exact resolve eq289376 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289376
  have eq289931 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq289468 eq111
    | exact resolve eq111 eq289468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq289468
  have eq289944 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq289931
  have eq289948 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq289944
    | exact resolve eq289944 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289944
  have eq289981 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq70 y y
       have i₂ := eq289948
       grind)
    | exact superpose eq289948 eq70
    | (have j0 := eq70 y y
       grind)
    | exact resolve eq70 eq289948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq289982 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq289981
  have eq290509 : (k y y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq289982
  have eq320697 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq289948
       have i₂ := eq290509
       grind)
    | exact superpose eq290509 eq289948
    | exact resolve eq289948 eq290509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289948 eq290509
  have eq320709 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq320697
  have eq320758 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq102
       have i₂ := eq320709
       grind)
    | exact superpose eq320709 eq102
    | exact resolve eq102 eq320709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq320767 : (σ (M.op x y)) = (σ (k x y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq6340 y
       have i₂ := eq320709
       grind)
    | exact superpose eq320709 eq6340
    | exact resolve eq6340 eq320709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6340 eq320709
  have eq320768 : (σ (M.op x y)) = (σ (k x y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq320767
  have eq320775 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq320758
  have eq320778 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq320768
       have i₂ := eq46
       grind)
    | exact superpose eq46 eq320768
    | exact resolve eq320768 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq320768
  have eq320784 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq320775
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq320775
    | exact resolve eq320775 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320775
  have eq320785 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq320778
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq320778
    | exact resolve eq320778 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320778
  have eq320790 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq22 eq320785
    | exact resolve eq320785 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320785
  have eq321706 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq3120 eq320784
    | exact resolve eq320784 eq3120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3120
  have eq329690 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq321706
  have eq372612 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq329690 eq320784
    | exact resolve eq320784 eq329690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320784 eq329690
  have eq372691 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq372612
  have eq372732 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq372691
  have eq372744 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq372732
  have eq372749 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq28 eq372744
    | exact resolve eq372744 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372744
  have eq373387 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq372749 eq320790
    | exact resolve eq320790 eq372749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320790 eq372749
  have eq373392 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq373387
  have eq373407 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq373392
       have r₂ := eq29
       grind)
    | exact resolve eq373392 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373392
  have eq373415 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq373407 eq180521
    | exact resolve eq180521 eq373407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180521 eq373407
  have eq373582 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq373415
  have eq373643 : x = y ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq179321
       have i₂ := eq373582
       grind)
    | exact superpose eq373582 eq179321
    | exact resolve eq179321 eq373582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179321 eq373582
  have eq373816 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq373643
  have eq373898 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq373816 eq31
    | exact resolve eq31 eq373816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq373816
  have eq374102 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq373898
    | exact resolve eq373898 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq373898
  have eq374103 : x = y := by grind
  clear eq374102
  have eq374106 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq374103
       grind)
    | exact superpose eq374103 eq20
    | exact resolve eq20 eq374103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq374107 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq374103
       grind)
    | exact superpose eq374103 eq26
    | exact resolve eq26 eq374103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq374855 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq374107
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq374107
    | exact resolve eq374107 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374107
  have eq374858 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq374855 eq28
    | exact resolve eq28 eq374855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq375236 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq374106
       grind)
    | exact superpose eq374106 eq103
    | exact resolve eq103 eq374106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq375329 : (k x (M.op x y)) = (M.op x (M.op x y)) := by grind
  have eq375341 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22 eq375236
    | exact resolve eq375236 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375236
  have eq375366 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq374858 eq13330
    | exact resolve eq13330 eq374858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13330
  have eq375453 : (k (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by grind
  have eq375459 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq374855 eq375366
    | exact resolve eq375366 eq374855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375366
  have eq375461 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq374855 eq375459
    | exact resolve eq375459 eq374855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374855 eq375459
  have eq375463 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq374858 eq375461
    | exact resolve eq375461 eq374858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375461
  have eq375464 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq375463
  have eq375467 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq375464
       have i₂ := eq374106
       grind)
    | exact superpose eq374106 eq375464
    | exact resolve eq375464 eq374106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375464
  have eq375469 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq375467
       have i₂ := eq374103
       grind)
    | exact superpose eq374103 eq375467
    | exact resolve eq375467 eq374103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375467
  have eq375471 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq375469
       have i₂ := eq374103
       grind)
    | exact superpose eq374103 eq375469
    | exact resolve eq375469 eq374103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374103 eq375469
  have eq375473 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq375471
       have i₂ := eq374106
       grind)
    | exact superpose eq374106 eq375471
    | exact resolve eq375471 eq374106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375471
  have eq375474 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq375473
  have eq375651 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq375474 eq375453
    | exact resolve eq375453 eq375474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375453 eq375474
  have eq375655 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq374858 eq375651
    | exact resolve eq375651 eq374858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375651
  have eq376331 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq375655 eq375341
    | exact resolve eq375341 eq375655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375341 eq375655
  have eq376349 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq376331
  have eq376358 : x = (M.op x y) := by
    first
    | (have r₁ := eq376349
       have r₂ := eq29
       grind)
    | exact resolve eq376349 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376349
  have eq376371 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq376358 eq22
    | exact resolve eq22 eq376358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq376623 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq376358 eq375329
    | exact resolve eq375329 eq376358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375329
  have eq376628 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq376623
       have i₂ := eq374106
       grind)
    | exact superpose eq374106 eq376623
    | exact resolve eq376623 eq374106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374106 eq376623
  have eq376795 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq376371
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq376371
    | exact resolve eq376371 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376371
  have eq376797 : x = (k x x) := by
    first
    | exact superpose eq376358 eq376628
    | exact resolve eq376628 eq376358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376358 eq376628
  have eq378443 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq390 x
       have i₂ := eq376797
       grind)
    | exact superpose eq376797 eq390
    | (have j0 := eq390 x
       grind)
    | exact resolve eq390 eq376797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390 eq376797
  have eq378465 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq378443
  have eq378485 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq378465
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq378465
    | exact resolve eq378465 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq378465
  have eq378511 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq374858 eq378485
    | exact resolve eq378485 eq374858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374858 eq378485
  have eq378533 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq376795 eq378511
    | exact resolve eq378511 eq376795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376795 eq378511
  have eq378553 : False := by grind
  exact eq378553

/-- `x □ y = if m(X,X) = Y then m(X,Y) else if X = Y then m(X,X) else if m(Y,Y) = X then m(X,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_y_x_y_pyy_x_pxy_pxx_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ a ≠ b ∨ k a b = M.op a a :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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

/-- `x □ y = if m(X,X) = Y then m(X,Y) else if X = Y then m(X,Y) else if m(Y,Y) = X then m(X,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_y_x_y_pyy_x_pxy_pxy_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ a ≠ b ∨ k a b = M.op a b :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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

/-- `x □ y = if m(X,X) = Y then m(X,Y) else if X = Y then m(Y,X) else if m(Y,Y) = X then m(X,Y)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_y_x_y_pyy_x_pxy_pyx_pxy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ a ≠ b ∨ k a b = M.op b a :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
