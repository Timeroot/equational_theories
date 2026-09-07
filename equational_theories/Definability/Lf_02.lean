import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyx_pxy_pyx_pxy_pyx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq21 (σ X0)
       grind)
    | exact superpose eq21 eq13
    | exact resolve eq13 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq23
    | exact resolve eq23 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq23
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
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
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq10 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq10 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq52 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq55 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq43
    | (have j0 := eq43 X0 X1
       grind)
    | exact resolve eq43 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq80 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X0) X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 (σ X0) X1
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq55 X0 X1
       grind)
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq11
    | (have j1 := eq55 X0 X1
       grind)
    | (have r₁ := eq11 (σ X1) (σ X0)
       have r₂ := eq55 X0 X1
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq55 X0 X1
       grind)
    | exact resolve eq11 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X0) (σ X1)
       have i₂ := eq55 X0 X1
       grind)
    | (have i₁ := eq10 (σ X1) (σ X0)
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq10
    | (have j0 := eq10 (σ X0) (σ X1)
       have j1 := eq55 X0 X1
       grind)
    | (have r₁ := eq10 (σ X1) (σ X1)
       have r₂ := eq55 X1 X1
       grind)
    | (have r₁ := eq10 (σ X0) (σ X0)
       have r₂ := eq55 X0 X0
       grind)
    | exact resolve eq10 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq178 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq160 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq183 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq161 X0 X1
       have j1 := eq80 X0 (σ X1)
       grind)
    | (have r₁ := eq161 X0 X1
       have r₂ := eq80 X0 (σ X1)
       grind)
    | exact resolve eq161 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq184 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq178 X0 X1
       have j1 := eq80 X0 (σ X1)
       grind)
    | (have r₁ := eq178 X0 X1
       have r₂ := eq80 X0 (σ X1)
       grind)
    | exact resolve eq178 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq178
  have eq205 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq183 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq183
    | (have j0 := eq183 X0 X1
       grind)
    | exact resolve eq183 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq206 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq184 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq184
    | (have j0 := eq184 X0 X1
       grind)
    | exact resolve eq184 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq184
  have eq219 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq205 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq205
    | (have j0 := eq205 X0 X1
       grind)
    | exact resolve eq205 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq220 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq219 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq221 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq206 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq206
    | (have j0 := eq206 X0 X1
       grind)
    | exact resolve eq206 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq222 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq221 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq228 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq222 X0 X1
       have j1 := eq220 X0 X1
       grind)
    | (have r₁ := eq222 X0 X1
       have r₂ := eq220 X0 X1
       grind)
    | exact resolve eq222 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq222
  have eq248 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq228 x y
       grind)
    | exact superpose eq228 eq14
    | exact resolve eq14 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq325 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq248
       have i₂ := eq52 x y
       grind)
    | exact superpose eq52 eq248
    | (have j1 := eq52 y x
       grind)
    | exact resolve eq248 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq328 : (M.op x y) = (M.op y x) := by grind
  clear eq325
  have eq385 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq328
       grind)
    | exact superpose eq328 eq11
    | (have r₁ := eq11 y x
       have r₂ := eq328
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq328
       grind)
    | exact resolve eq11 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq386 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq10 x y
       have i₂ := eq328
       grind)
    | exact superpose eq328 eq10
    | (have j0 := eq10 x y
       grind)
    | exact resolve eq10 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq387 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
  clear eq385
  have eq389 : (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq387
       have r₂ := eq386
       grind)
    | exact resolve eq387 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386 eq387
  have eq449 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq248
       have i₂ := eq389
       grind)
    | exact superpose eq389 eq248
    | exact resolve eq248 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq389
  have eq450 : False := by grind
  exact eq450

/-- `x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyx_pxy_pyy_pxy_pyy_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq10 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq10 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
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
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq62 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq63 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq64 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq73 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       have j1 := eq10 X1 X0
       grind)
    | (have r₁ := eq62 X1 X1
       have r₂ := eq10 X1 X1
       grind)
    | (have r₁ := eq62 X1 X0
       have r₂ := eq10 X0 X1
       grind)
    | exact resolve eq62 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq193 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq73 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq198 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq193 X0 X1
       have j1 := eq64 X0 X1
       grind)
    | (have r₁ := eq193 X0 X1
       have r₂ := eq64 X0 X1
       grind)
    | (have r₁ := eq193 X0 X0
       have r₂ := eq64 X0 X0
       grind)
    | exact resolve eq193 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq193
  have eq223 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq198 (σ X0) (σ X1)
       grind)
    | exact superpose eq198 eq13
    | exact resolve eq13 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq223 X0 X1
       have i₂ := eq198 X0 X1
       grind)
    | exact superpose eq198 eq223
    | exact resolve eq223 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq223
  have eq1566 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq230 x y
       grind)
    | exact superpose eq230 eq14
    | (have r₁ := eq14
       have r₂ := eq230 x y
       grind)
    | exact resolve eq14 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq1592 : False := by grind
  exact eq1592

/-- `x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyx_pxy_x_pxy_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
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
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq21 (σ X0)
       grind)
    | exact superpose eq21 eq13
    | exact resolve eq13 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq23
    | exact resolve eq23 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq23
  have eq48 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq10 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq10 X1 (M.op X1 X1)
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq50 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq50 (σ X0) (σ X1)
       grind)
    | exact superpose eq50 eq13
    | (have j1 := eq50 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
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
  clear eq16 eq50
  have eq77 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X0) X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 (σ X0) X1
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq393 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq71 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq71
    | exact resolve eq71 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq433 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq393 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq393
    | (have j0 := eq393 X0 X1
       grind)
    | exact resolve eq393 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq603 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq68 x y
       grind)
    | exact superpose eq68 eq14
    | (have j1 := eq68 x y
       grind)
    | exact resolve eq14 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq612 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq2464 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq603
       have i₂ := eq433 y x
       grind)
    | exact superpose eq433 eq603
    | (have j1 := eq433 (σ y) (σ x)
       grind)
    | (have r₁ := eq603
       have r₂ := eq433 y x
       grind)
    | exact resolve eq603 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq2465 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2464
  have eq2469 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2465
       grind)
    | exact superpose eq2465 eq14
    | exact resolve eq14 eq2465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2470 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq2465
       grind)
    | exact superpose eq2465 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq2465
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq2465
       grind)
    | exact resolve eq11 eq2465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2471 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2470
  have eq2472 : (σ (M.op x x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2471
       have i₂ := eq26 x
       grind)
    | exact superpose eq26 eq2471
    | exact resolve eq2471 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2471
  have eq2474 : (σ (M.op x x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2472
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq2472
    | exact resolve eq2472 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2472
  have eq42634 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq77 x (σ y)
       have i₂ := eq2474
       grind)
    | exact superpose eq2474 eq77
    | (have j0 := eq77 x (σ y)
       grind)
    | (have r₁ := eq77 x (σ y)
       have r₂ := eq2474
       grind)
    | exact resolve eq77 eq2474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq2474
  have eq42638 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by grind
  clear eq42634
  have eq42642 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq42638
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq42638
    | exact resolve eq42638 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42638
  have eq73100 : (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2465
       have i₂ := eq42642
       grind)
    | exact superpose eq42642 eq2465
    | exact resolve eq2465 eq42642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2465 eq42642
  have eq73109 : (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by grind
  clear eq73100
  have eq74230 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq433 y x
       have i₂ := eq73109
       grind)
    | exact superpose eq73109 eq433
    | (have j0 := eq433 y x
       grind)
    | exact resolve eq433 eq73109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433 eq73109
  have eq74312 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq74230
  have eq74337 : x = (M.op x y) := by
    first
    | (have r₁ := eq74312
       have r₂ := eq2469
       grind)
    | exact resolve eq74312 eq2469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2469 eq74312
  have eq75398 : x ≠ x ∨ (M.op x x) = (M.op y x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq74337
       grind)
    | exact superpose eq74337 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq74337
       grind)
    | exact resolve eq11 eq74337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75399 : x = (k x y) ∨ (M.op x x) = (M.op y x) := by grind
  clear eq75398
  have eq75744 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq612 x y
       have i₂ := eq75399
       grind)
    | exact superpose eq75399 eq612
    | (have j0 := eq612 x y
       grind)
    | exact resolve eq612 eq75399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75399
  have eq75813 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y x) := by grind
  clear eq75744
  have eq77241 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq75813
       grind)
    | exact superpose eq75813 eq14
    | exact resolve eq14 eq75813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75813
  have eq77249 : (σ x) ≠ (σ x) ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq77241
       have i₂ := eq74337
       grind)
    | exact superpose eq74337 eq77241
    | exact resolve eq77241 eq74337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77241
  have eq77250 : (M.op x x) = (M.op y x) := by grind
  clear eq77249
  have eq78338 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq10 x y
       have i₂ := eq77250
       grind)
    | exact superpose eq77250 eq10
    | (have j0 := eq10 x x
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq77250
       grind)
    | exact resolve eq10 eq77250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77250
  have eq78351 : (M.op x y) = (k x y) := by grind
  clear eq78338
  have eq78353 : x = (k x y) := by
    first
    | (have i₁ := eq78351
       have i₂ := eq74337
       grind)
    | exact superpose eq74337 eq78351
    | exact resolve eq78351 eq74337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78351
  have eq79461 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq612 x y
       have i₂ := eq78353
       grind)
    | exact superpose eq78353 eq612
    | (have j0 := eq612 x y
       grind)
    | exact resolve eq612 eq78353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612 eq78353
  have eq79532 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq79461
  have eq80177 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq79532
       grind)
    | exact superpose eq79532 eq14
    | exact resolve eq14 eq79532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79532
  have eq80185 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq80177
       have i₂ := eq74337
       grind)
    | exact superpose eq74337 eq80177
    | exact resolve eq80177 eq74337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74337 eq80177
  have eq80186 : False := by grind
  exact eq80186

/-- `x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyx_pxy_y_pxy_y_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq21 (σ X0)
       grind)
    | exact superpose eq21 eq13
    | exact resolve eq13 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq23
    | exact resolve eq23 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq23
  have eq48 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq10 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq50 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq50 (σ X0) (σ X1)
       grind)
    | exact superpose eq50 eq13
    | (have j1 := eq50 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq50 (τ X0) X1
       grind)
    | exact superpose eq50 eq15
    | (have j1 := eq50 (τ X0) X1
       grind)
    | exact resolve eq15 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq50
  have eq77 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X0) X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 (σ X0) X1
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq393 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq69
    | exact resolve eq69 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq433 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq393 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq393
    | (have j0 := eq393 X0 X1
       grind)
    | exact resolve eq393 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq603 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq68 x y
       grind)
    | exact superpose eq68 eq14
    | (have j1 := eq68 x y
       grind)
    | exact resolve eq14 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq612 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq2498 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq603
       have i₂ := eq433 x y
       grind)
    | exact superpose eq433 eq603
    | (have j1 := eq433 (σ x) (σ y)
       grind)
    | (have r₁ := eq603
       have r₂ := eq433 x y
       grind)
    | exact resolve eq603 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq2499 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2498
  have eq2503 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2499
       grind)
    | exact superpose eq2499 eq14
    | exact resolve eq14 eq2499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2504 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq2499
       grind)
    | exact superpose eq2499 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq2499
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq2499
       grind)
    | exact resolve eq11 eq2499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2505 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2504
  have eq2506 : (σ (M.op x x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2505
       have i₂ := eq26 x
       grind)
    | exact superpose eq26 eq2505
    | exact resolve eq2505 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2505
  have eq2508 : (σ (M.op x x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2506
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq2506
    | exact resolve eq2506 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2506
  have eq38804 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq77 x (σ y)
       have i₂ := eq2508
       grind)
    | exact superpose eq2508 eq77
    | (have j0 := eq77 x (σ y)
       grind)
    | (have r₁ := eq77 x (σ y)
       have r₂ := eq2508
       grind)
    | exact resolve eq77 eq2508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq2508
  have eq38808 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by grind
  clear eq38804
  have eq38812 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq38808
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq38808
    | exact resolve eq38808 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38808
  have eq68264 : (σ y) = (σ (k x y)) ∨ y = (M.op x y) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2499
       have i₂ := eq38812
       grind)
    | exact superpose eq38812 eq2499
    | exact resolve eq2499 eq38812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2499 eq38812
  have eq68273 : (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by grind
  clear eq68264
  have eq69373 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq433 x y
       have i₂ := eq68273
       grind)
    | exact superpose eq68273 eq433
    | (have j0 := eq433 x y
       grind)
    | exact resolve eq433 eq68273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433 eq68273
  have eq69455 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq69373
  have eq69480 : y = (M.op x y) := by
    first
    | (have r₁ := eq69455
       have r₂ := eq2503
       grind)
    | exact resolve eq69455 eq2503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2503 eq69455
  have eq70322 : y ≠ y ∨ (M.op x x) = (M.op y x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq69480
       grind)
    | exact superpose eq69480 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq69480
       grind)
    | exact resolve eq11 eq69480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70323 : y = (k x y) ∨ (M.op x x) = (M.op y x) := by grind
  clear eq70322
  have eq71128 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq612 x y
       have i₂ := eq70323
       grind)
    | exact superpose eq70323 eq612
    | (have j0 := eq612 x y
       grind)
    | exact resolve eq612 eq70323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70323
  have eq71197 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y x) := by grind
  clear eq71128
  have eq72857 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq71197
       grind)
    | exact superpose eq71197 eq14
    | exact resolve eq14 eq71197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71197
  have eq72865 : (σ y) ≠ (σ y) ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq72857
       have i₂ := eq69480
       grind)
    | exact superpose eq69480 eq72857
    | exact resolve eq72857 eq69480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72857
  have eq72866 : (M.op x x) = (M.op y x) := by grind
  clear eq72865
  have eq73727 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq10 x y
       have i₂ := eq72866
       grind)
    | exact superpose eq72866 eq10
    | (have j0 := eq10 x x
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq72866
       grind)
    | exact resolve eq10 eq72866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72866
  have eq73740 : (M.op x y) = (k x y) := by grind
  clear eq73727
  have eq73742 : y = (k x y) := by
    first
    | (have i₁ := eq73740
       have i₂ := eq69480
       grind)
    | exact superpose eq69480 eq73740
    | exact resolve eq73740 eq69480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73740
  have eq74564 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq612 x y
       have i₂ := eq73742
       grind)
    | exact superpose eq73742 eq612
    | (have j0 := eq612 x y
       grind)
    | exact resolve eq612 eq73742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612 eq73742
  have eq74635 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq74564
  have eq76326 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq74635
       grind)
    | exact superpose eq74635 eq14
    | exact resolve eq14 eq74635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74635
  have eq76334 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq76326
       have i₂ := eq69480
       grind)
    | exact superpose eq69480 eq76326
    | exact resolve eq76326 eq69480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69480 eq76326
  have eq76335 : False := by grind
  exact eq76335

/-- `x □ y = if m(X,X) = m(Y,X) then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyx_pyx_pyy_pxx_pyy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X1 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       have j1 := eq59 X0 X1
       grind)
    | (have r₁ := eq61 X0 X1
       have r₂ := eq59 X0 X1
       grind)
    | (have r₁ := eq61 X1 X0
       have r₂ := eq59 X0 X1
       grind)
    | (have r₁ := eq61 X1 X1
       have r₂ := eq59 X1 X1
       grind)
    | exact resolve eq61 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq61
  have eq334 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq67 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq347 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq334 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq334 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq334 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq334 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq334 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq536 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq347 X0 X1
       grind)
    | (have i₁ := eq10 X0 X0
       have i₂ := eq347 X0 X1
       grind)
    | exact superpose eq347 eq10
    | (have j0 := eq10 X0 X0
       have j1 := eq347 X0 X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq347 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq347 X0 X0
       grind)
    | exact resolve eq10 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq549 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq536 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq892 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq549 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq903 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq892 X0 X1
       have j1 := eq347 X0 X1
       grind)
    | (have r₁ := eq892 X0 X1
       have r₂ := eq347 X0 X1
       grind)
    | (have r₁ := eq892 X0 X0
       have r₂ := eq347 X0 X0
       grind)
    | exact resolve eq892 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347 eq892
  have eq1175 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq903 (σ X1) (σ X0)
       grind)
    | exact superpose eq903 eq13
    | exact resolve eq13 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1186 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1175 X0 X1
       have i₂ := eq903 X1 X0
       grind)
    | exact superpose eq903 eq1175
    | exact resolve eq1175 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903 eq1175
  have eq2811 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1186 x y
       grind)
    | exact superpose eq1186 eq14
    | (have r₁ := eq14
       have r₂ := eq1186 x y
       grind)
    | exact resolve eq14 eq1186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186
  have eq2870 : False := by grind
  exact eq2870

/-- `x □ y = if m(X,X) = m(Y,X) then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyx_pyx_x_pxx_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
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
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq21 (σ X0)
       grind)
    | exact superpose eq21 eq13
    | exact resolve eq13 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq23
    | exact resolve eq23 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq23
  have eq42 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq10 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq52 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq42
    | (have j0 := eq42 X0 X1
       grind)
    | exact resolve eq42 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq74 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X0) X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq10
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq49 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq49
    | (have j0 := eq49 (σ X0) (σ X1)
       grind)
    | exact resolve eq49 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq101 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq98 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq98 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq98 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq98 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq106 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq82 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq82
    | (have j0 := eq82 X0 X1
       grind)
    | exact resolve eq82 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq213 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq219 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq213 X0 X1
       have j1 := eq106 X1 X0
       grind)
    | (have r₁ := eq213 X1 X0
       have r₂ := eq106 X0 X1
       grind)
    | exact resolve eq213 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq213
  have eq386 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq101 X1 (τ X0)
       grind)
    | exact superpose eq101 eq16
    | (have j1 := eq101 X1 (τ X0)
       grind)
    | exact resolve eq16 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq101
  have eq659 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq219 x y
       grind)
    | exact superpose eq219 eq14
    | (have j1 := eq219 x y
       grind)
    | exact resolve eq14 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq673 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq219 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq2044 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq386 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq386
    | exact resolve eq386 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq2131 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2044 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq2044
    | (have j0 := eq2044 X0 X1
       grind)
    | exact resolve eq2044 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2044
  have eq2877 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq659
       have i₂ := eq2131 x y
       grind)
    | exact superpose eq2131 eq659
    | (have j1 := eq2131 (σ x) (σ y)
       grind)
    | (have r₁ := eq659
       have r₂ := eq2131 x y
       grind)
    | exact resolve eq659 eq2131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq2878 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2877
  have eq3179 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2878
       grind)
    | exact superpose eq2878 eq14
    | exact resolve eq14 eq2878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3180 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ y) (σ x)
       have i₂ := eq2878
       grind)
    | exact superpose eq2878 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq2878
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq2878
       grind)
    | exact resolve eq11 eq2878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3183 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq3180
  have eq3186 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3183
       have i₂ := eq26 y
       grind)
    | exact superpose eq26 eq3183
    | exact resolve eq3183 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq3183
  have eq3191 : (σ y) = (σ (k y x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3186
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq3186
    | exact resolve eq3186 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3186
  have eq12748 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2131 x y
       have i₂ := eq3191
       grind)
    | exact superpose eq3191 eq2131
    | (have j0 := eq2131 x y
       grind)
    | exact resolve eq2131 eq3191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3191
  have eq12823 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq12748
  have eq12855 : (σ y) = (σ (M.op y y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq12823
       have r₂ := eq3179
       grind)
    | exact resolve eq12823 eq3179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12823
  have eq13217 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ y)) ∨ (σ y) = (k (σ y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq74 y x
       have i₂ := eq12855
       grind)
    | exact superpose eq12855 eq74
    | exact resolve eq74 eq12855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq12855
  have eq49923 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13217 (σ x)
       have i₂ := eq2878
       grind)
    | exact superpose eq2878 eq13217
    | (have j0 := eq13217 (σ x)
       grind)
    | (have r₁ := eq13217 (σ x)
       have r₂ := eq2878
       grind)
    | exact resolve eq13217 eq2878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2878 eq13217
  have eq49924 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq49923
  have eq49925 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq49924
  have eq49929 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq49925
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq49925
    | exact resolve eq49925 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49925
  have eq50625 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2131 x y
       have i₂ := eq49929
       grind)
    | exact superpose eq49929 eq2131
    | (have j0 := eq2131 x y
       grind)
    | exact resolve eq2131 eq49929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2131 eq49929
  have eq50672 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq50625
  have eq50701 : y = (M.op x y) := by
    first
    | (have r₁ := eq50672
       have r₂ := eq3179
       grind)
    | exact resolve eq50672 eq3179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3179 eq50672
  have eq51311 : y ≠ y ∨ y = (M.op y y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq50701
       grind)
    | exact superpose eq50701 eq11
    | (have j0 := eq11 y x
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq50701
       grind)
    | exact resolve eq11 eq50701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51313 : y = (k y x) ∨ y = (M.op y y) := by grind
  clear eq51311
  have eq52217 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq673 x y
       have i₂ := eq51313
       grind)
    | exact superpose eq51313 eq673
    | (have j0 := eq673 x y
       grind)
    | exact resolve eq673 eq51313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51313
  have eq52242 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq52217
  have eq54017 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq52242
       grind)
    | exact superpose eq52242 eq14
    | exact resolve eq14 eq52242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52242
  have eq54025 : (σ y) ≠ (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq54017
       have i₂ := eq50701
       grind)
    | exact superpose eq50701 eq54017
    | exact resolve eq54017 eq50701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54017
  have eq54026 : y = (M.op y y) := by grind
  clear eq54025
  have eq54896 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq10 y x
       have i₂ := eq54026
       grind)
    | exact superpose eq54026 eq10
    | exact resolve eq10 eq54026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54026
  have eq55227 : y ≠ y ∨ y = (k y x) := by
    first
    | (have i₁ := eq54896 x
       have i₂ := eq50701
       grind)
    | exact superpose eq50701 eq54896
    | (have j0 := eq54896 x
       grind)
    | (have r₁ := eq54896 x
       have r₂ := eq50701
       grind)
    | exact resolve eq54896 eq50701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54896
  have eq55232 : y = (k y x) := by grind
  clear eq55227
  have eq56163 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq673 x y
       have i₂ := eq55232
       grind)
    | exact superpose eq55232 eq673
    | (have j0 := eq673 x y
       grind)
    | exact resolve eq673 eq55232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673 eq55232
  have eq56187 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq56163
  have eq57985 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq56187
       grind)
    | exact superpose eq56187 eq14
    | exact resolve eq14 eq56187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56187
  have eq57994 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq57985
       have i₂ := eq50701
       grind)
    | exact superpose eq50701 eq57985
    | exact resolve eq57985 eq50701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50701 eq57985
  have eq57995 : False := by grind
  exact eq57995

/-- `x □ y = if m(X,X) = m(Y,X) then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyx_pyx_y_pxx_y_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq21 (σ X0)
       grind)
    | exact superpose eq21 eq13
    | exact resolve eq13 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq23
    | exact resolve eq23 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq23
  have eq42 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq10 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq10 X0 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq52 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq42
    | (have j0 := eq42 X0 X1
       grind)
    | exact resolve eq42 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq75 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (σ X0) X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq10
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq49 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq49
    | (have j0 := eq49 (σ X0) (σ X1)
       grind)
    | exact resolve eq49 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq102 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq99 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq99 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq99 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq99 X0 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq99 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq107 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq83
    | (have j0 := eq83 X0 X1
       grind)
    | exact resolve eq83 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq212 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq216 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq212 X0 X1
       have j1 := eq107 X1 X0
       grind)
    | (have r₁ := eq212 X1 X0
       have r₂ := eq107 X0 X1
       grind)
    | exact resolve eq212 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq212
  have eq365 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq102 (τ X1) X0
       grind)
    | exact superpose eq102 eq15
    | (have j1 := eq102 (τ X1) X0
       grind)
    | exact resolve eq15 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq102
  have eq641 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq216 x y
       grind)
    | exact superpose eq216 eq14
    | (have j1 := eq216 x y
       grind)
    | exact resolve eq14 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq655 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq216 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq2031 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq365 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq365
    | exact resolve eq365 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq2114 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2031 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2031
    | (have j0 := eq2031 X0 X1
       grind)
    | exact resolve eq2031 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2031
  have eq2593 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq641
       have i₂ := eq2114 y x
       grind)
    | exact superpose eq2114 eq641
    | (have j1 := eq2114 (σ y) (σ x)
       grind)
    | (have r₁ := eq641
       have r₂ := eq2114 y x
       grind)
    | exact resolve eq641 eq2114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq2594 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2593
  have eq2618 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2594
       grind)
    | exact superpose eq2594 eq14
    | exact resolve eq14 eq2594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2619 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ y) (σ x)
       have i₂ := eq2594
       grind)
    | exact superpose eq2594 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq2594
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq2594
       grind)
    | exact resolve eq11 eq2594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2622 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq2619
  have eq2623 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2622
       have i₂ := eq26 y
       grind)
    | exact superpose eq26 eq2622
    | exact resolve eq2622 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2622
  have eq2627 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2623
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq2623
    | exact resolve eq2623 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2623
  have eq12016 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2114 y x
       have i₂ := eq2627
       grind)
    | exact superpose eq2627 eq2114
    | (have j0 := eq2114 y x
       grind)
    | exact resolve eq2114 eq2627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2627
  have eq12092 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq12016
  have eq12124 : (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq12092
       have r₂ := eq2618
       grind)
    | exact resolve eq12092 eq2618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12092
  have eq12453 : ∀ X0 : G, (σ x) ≠ (M.op X0 (σ y)) ∨ (σ x) = (k (σ y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq75 y x
       have i₂ := eq12124
       grind)
    | exact superpose eq12124 eq75
    | exact resolve eq75 eq12124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq12124
  have eq39085 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12453 (σ x)
       have i₂ := eq2594
       grind)
    | exact superpose eq2594 eq12453
    | (have j0 := eq12453 (σ x)
       grind)
    | (have r₁ := eq12453 (σ x)
       have r₂ := eq2594
       grind)
    | exact resolve eq12453 eq2594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2594 eq12453
  have eq39086 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq39085
  have eq39087 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq39086
  have eq39088 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39087
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq39087
    | exact resolve eq39087 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39087
  have eq39563 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2114 y x
       have i₂ := eq39088
       grind)
    | exact superpose eq39088 eq2114
    | (have j0 := eq2114 y x
       grind)
    | exact resolve eq2114 eq39088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2114 eq39088
  have eq39606 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq39563
  have eq39635 : x = (M.op x y) := by
    first
    | (have r₁ := eq39606
       have r₂ := eq2618
       grind)
    | exact resolve eq39606 eq2618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2618 eq39606
  have eq40233 : x ≠ x ∨ x = (M.op y y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq39635
       grind)
    | exact superpose eq39635 eq11
    | (have j0 := eq11 y x
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq39635
       grind)
    | exact resolve eq11 eq39635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40235 : x = (k y x) ∨ x = (M.op y y) := by grind
  clear eq40233
  have eq40779 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq655 x y
       have i₂ := eq40235
       grind)
    | exact superpose eq40235 eq655
    | (have j0 := eq655 x y
       grind)
    | exact resolve eq655 eq40235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40235
  have eq40804 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq40779
  have eq41910 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq40804
       grind)
    | exact superpose eq40804 eq14
    | exact resolve eq14 eq40804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40804
  have eq41918 : (σ x) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq41910
       have i₂ := eq39635
       grind)
    | exact superpose eq39635 eq41910
    | exact resolve eq41910 eq39635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41910
  have eq41919 : x = (M.op y y) := by grind
  clear eq41918
  have eq42148 : ∀ X0 : G, x ≠ (M.op X0 y) ∨ x = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq10 y x
       have i₂ := eq41919
       grind)
    | exact superpose eq41919 eq10
    | exact resolve eq10 eq41919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41919
  have eq42721 : x ≠ x ∨ x = (k y x) := by
    first
    | (have i₁ := eq42148 x
       have i₂ := eq39635
       grind)
    | exact superpose eq39635 eq42148
    | (have j0 := eq42148 x
       grind)
    | (have r₁ := eq42148 x
       have r₂ := eq39635
       grind)
    | exact resolve eq42148 eq39635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42148
  have eq42726 : x = (k y x) := by grind
  clear eq42721
  have eq43282 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq655 x y
       have i₂ := eq42726
       grind)
    | exact superpose eq42726 eq655
    | (have j0 := eq655 x y
       grind)
    | exact resolve eq655 eq42726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655 eq42726
  have eq43306 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq43282
  have eq44425 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq43306
       grind)
    | exact superpose eq43306 eq14
    | exact resolve eq14 eq43306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43306
  have eq44434 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq44425
       have i₂ := eq39635
       grind)
    | exact superpose eq39635 eq44425
    | exact resolve eq44425 eq39635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39635 eq44425
  have eq44435 : False := by grind
  exact eq44435

/-- `x □ y = if m(X,X) = m(Y,X) then m(X,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pxx_pyx_x_y_pxx_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
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
  have eq10 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq22 (σ X0)
       grind)
    | exact superpose eq22 eq13
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq24
  have eq32 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq10 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq40 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq27 X1
       grind)
    | exact superpose eq27 eq32
    | (have j0 := eq32 X0 X1
       grind)
    | exact resolve eq32 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq37
    | (have j0 := eq37 (σ (k X0 X1)) (M.op (σ X0) (σ X0))
       grind)
    | exact resolve eq37 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq72 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq69 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq69 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq69 X0 X1
       have r₂ := eq12 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq69 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1
       have i₂ := eq27 X0
       grind)
    | exact superpose eq27 eq57
    | (have j0 := eq57 X0 X1
       grind)
    | exact resolve eq57 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq151 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq158 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq151 X0 X1
       have j1 := eq77 X1 X0
       grind)
    | (have r₁ := eq151 X1 X0
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq151 X0 X1
       have r₂ := eq77 (k X1 X0) (M.op X1 X1)
       grind)
    | (have r₁ := eq151 X0 X1
       have r₂ := eq77 (M.op X1 X1) (k X1 X0)
       grind)
    | exact resolve eq151 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq151
  have eq276 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq72 (τ X1) X0
       grind)
    | exact superpose eq72 eq16
    | (have j1 := eq72 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq72
  have eq575 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq276 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq276
    | exact resolve eq276 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq612 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq575 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq575
    | (have j0 := eq575 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq575 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq629 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq158 x y
       grind)
    | exact superpose eq158 eq14
    | (have j1 := eq158 x y
       grind)
    | exact resolve eq14 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq1063 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq629
       have i₂ := eq612 y x
       grind)
    | exact superpose eq612 eq629
    | (have j1 := eq612 (σ x) (σ y)
       grind)
    | (have r₁ := eq629
       have r₂ := eq612 y x
       grind)
    | (have r₁ := eq629
       have r₂ := eq612 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq629
       have r₂ := eq612 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq629 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612 eq629
  have eq1064 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1063
  have eq1179 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq1064
       grind)
    | exact superpose eq1064 eq8
    | exact resolve eq8 eq1064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064
  have eq1215 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1179
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq1179
    | exact resolve eq1179 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179
  have eq1216 : x = y := by grind
  clear eq1215
  have eq1343 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1216
       grind)
    | exact superpose eq1216 eq14
    | exact resolve eq14 eq1216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1216
  have eq1344 : False := by grind
  exact eq1344
