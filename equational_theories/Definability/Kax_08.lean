import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3300`: `x ◇ x = y ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_pyy_pxx_pxy_Equation3300 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3300 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op x y) (M.op y y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1a | h1a
    · have b0e13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e17 : (M.op x y) = (M.op y y) := by grind
      have b0e18 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b0e19 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e16
        | exact resolve b0e16 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e20 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e19
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e19
        | exact resolve b0e19 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e19
      have b0e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e13 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e60 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e15 X0 X0
           have i₂ := b0e51 (σ X0)
           grind)
        | exact superpose b0e51 b0e15
        | exact resolve b0e15 b0e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e60 X0
           have i₂ := b0e51 X0
           grind)
        | exact superpose b0e51 b0e60
        | exact resolve b0e60 b0e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e51 b0e60
      have b0e480 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e20
           have i₂ := b0e65 y
           grind)
        | exact superpose b0e65 b0e20
        | (have r₁ := b0e20
           have r₂ := b0e65 y
           grind)
        | exact resolve b0e20 b0e65
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e20 b0e65
      have b0e496 : False := by grind
      exact b0e496
    · have b1e10 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X3 X0))) := by
        intro X0 X1 X2 X3
        grind
      have b1e13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b1e14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b1e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b1e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b1e17 : (M.op x y) = (M.op y y) := by grind
      have b1e18 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b1e19 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b1e16
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e16
        | exact resolve b1e16 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e43 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (k x y) := by
        first
        | (have i₁ := b1e13 x y
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e13
        | (have j0 := b1e13 y y
           grind)
        | (have r₁ := b1e13 x y
           have r₂ := b1e17
           grind)
        | exact resolve b1e13 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e48 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b1e13 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e50 : (M.op x x) = (k x y) := by grind
      clear b1e43
      have b1e54 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b1e15 X0 X0
           have i₂ := b1e48 (σ X0)
           grind)
        | exact superpose b1e48 b1e15
        | exact resolve b1e15 b1e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e59 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b1e54 X0
           have i₂ := b1e48 X0
           grind)
        | exact superpose b1e48 b1e54
        | exact resolve b1e54 b1e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e48 b1e54
      have b1e78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e15 X0 X1
           have i₂ := b1e14 (σ X0) (σ X1)
           grind)
        | exact superpose b1e14 b1e15
        | (have j1 := b1e14 (σ X0) (σ X1)
           grind)
        | exact resolve b1e15 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e83 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e78 X0 X1
           have i₂ := b1e59 X1
           grind)
        | exact superpose b1e59 b1e78
        | (have j0 := b1e78 X0 X1
           grind)
        | exact resolve b1e78 b1e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e78
      have b1e589 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op X1 (M.op X2 (σ (M.op X0 X0)))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e10 (σ X0) X1 X2 (σ X0)
           have i₂ := b1e59 X0
           grind)
        | exact superpose b1e59 b1e10
        | exact resolve b1e10 b1e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e1811 : (M.op (σ y) (σ y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e83 x y
           grind)
        | exact superpose b1e83 b1e18
        | (have j1 := b1e83 x y
           grind)
        | exact resolve b1e18 b1e83
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e1828 : ∀ X0 X1 X2 X3 : G, (M.op (σ X1) (σ X1)) = (M.op X2 (M.op X3 (σ (k X0 X1)))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 (σ X1) X2 X3 (σ X0)
           have i₂ := b1e83 X0 X1
           grind)
        | exact superpose b1e83 b1e10
        | (have j1 := b1e83 X0 X1
           grind)
        | exact resolve b1e10 b1e83
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e83
      have b1e1850 : ∀ X0 X1 X2 X3 : G, (σ (M.op X1 X1)) = (M.op X2 (M.op X3 (σ (k X0 X1)))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e1828 X0 X1 X2 X3
           have i₂ := b1e59 X1
           grind)
        | exact superpose b1e59 b1e1828
        | (have j0 := b1e1828 X0 X1 X2 X3
           grind)
        | exact resolve b1e1828 b1e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1828
      have b1e1851 : (M.op (σ y) (σ y)) ≠ (σ (k x y)) := by
        first
        | (have r₁ := b1e1811
           have r₂ := b1e19
           grind)
        | exact resolve b1e1811 b1e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1811
      have b1e1888 : (M.op (σ y) (σ y)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b1e1851
           have i₂ := b1e50
           grind)
        | exact superpose b1e50 b1e1851
        | exact resolve b1e1851 b1e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1851
      have b1e1907 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b1e1888
           have i₂ := b1e59 y
           grind)
        | exact superpose b1e59 b1e1888
        | exact resolve b1e1888 b1e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e59 b1e1888
      have b1e115603 : ∀ X0 X1 : G, (σ (M.op y y)) = (M.op X0 (M.op X1 (σ (M.op x x)))) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
        intro X0 X1
        first
        | (have i₁ := b1e1850 x y X0 X1
           have i₂ := b1e50
           grind)
        | exact superpose b1e50 b1e1850
        | (have j0 := b1e1850 x y x x
           grind)
        | exact resolve b1e1850 b1e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e50 b1e1850
      have b1e116381 : ∀ X0 X1 : G, (σ (M.op y y)) = (M.op X0 (M.op X1 (σ (M.op x x)))) := by
        intro X0 X1
        first
        | (have j0 := b1e115603 X0 X1
           grind)
        | (have r₁ := b1e115603 X0 X1
           have r₂ := b1e19
           grind)
        | exact resolve b1e115603 b1e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e19 b1e115603
      have b1e116573 : (σ (M.op y y)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b1e116381 x x
           have i₂ := b1e589 x x x
           grind)
        | exact superpose b1e589 b1e116381
        | exact resolve b1e116381 b1e589
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e589 b1e116381
      have b1e116732 : False := by grind
      exact b1e116732
  · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1a | h1a
    · have b2e10 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X3 X0))) := by
        intro X0 X1 X2 X3
        grind
      have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b2e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b2e17 : (M.op x y) ≠ (M.op y y) := by grind
      have b2e18 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b2e45 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
        first
        | (have i₁ := b2e13 (σ x) (σ y)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e13
        | (have j0 := b2e13 (σ y) (σ y)
           grind)
        | (have r₁ := b2e13 (σ x) (σ y)
           have r₂ := b2e18
           grind)
        | exact resolve b2e13 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e48 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b2e13 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e49 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
      clear b2e45
      have b2e52 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b2e49
           have i₂ := b2e15 x y
           grind)
        | exact superpose b2e15 b2e49
        | exact resolve b2e49 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e49
      have b2e91 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
        first
        | (have i₁ := b2e13 (σ x) (σ x)
           have i₂ := b2e52
           grind)
        | exact superpose b2e52 b2e13
        | exact resolve b2e13 b2e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e52
      have b2e93 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
      clear b2e91
      have b2e94 : (σ (k x y)) = (σ (k x x)) := by
        first
        | (have i₁ := b2e93
           have i₂ := b2e15 x x
           grind)
        | exact superpose b2e15 b2e93
        | exact resolve b2e93 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e93
      have b2e95 : (σ (k x y)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b2e94
           have i₂ := b2e48 x
           grind)
        | exact superpose b2e48 b2e94
        | exact resolve b2e94 b2e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e48 b2e94
      have b2e145 : (k x y) = (τ (σ (M.op x x))) := by
        first
        | (have i₁ := b2e11 (k x y)
           have i₂ := b2e95
           grind)
        | exact superpose b2e95 b2e11
        | exact resolve b2e11 b2e95
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e95
      have b2e146 : (k x y) = (M.op x x) := by
        first
        | (have i₁ := b2e145
           have i₂ := b2e11 (M.op x x)
           grind)
        | exact superpose b2e11 b2e145
        | exact resolve b2e145 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e145
      have b2e190 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b2e14 x y
           have i₂ := b2e146
           grind)
        | exact superpose b2e146 b2e14
        | (have j0 := b2e14 x y
           grind)
        | exact resolve b2e14 b2e146
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e146
      have b2e191 : (M.op x y) = (M.op x x) := by
        first
        | (have r₁ := b2e190
           have r₂ := b2e17
           grind)
        | exact resolve b2e190 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e190
      have b2e277 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X1 (M.op x y))) := by
        intro X0 X1
        first
        | (have i₁ := b2e10 x X1 x x
           have i₂ := b2e191
           grind)
        | exact superpose b2e191 b2e10
        | exact resolve b2e10 b2e191
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e191
      have b2e279 : (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b2e277 x x
           have i₂ := b2e10 y x x x
           grind)
        | (have i₁ := b2e277 (M.op x (M.op x y)) x
           have i₂ := b2e10 (M.op x (M.op x y)) x x x
           grind)
        | exact superpose b2e10 b2e277
        | exact resolve b2e277 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e277
      have b2e282 : False := by grind
      exact b2e282
    · have b3e13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b3e14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e17 : (M.op x y) ≠ (M.op y y) := by grind
      have b3e18 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e45 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b3e13 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e50 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b3e15 X0 X0
           have i₂ := b3e45 (σ X0)
           grind)
        | exact superpose b3e45 b3e15
        | exact resolve b3e15 b3e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e55 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b3e50 X0
           have i₂ := b3e45 X0
           grind)
        | exact superpose b3e45 b3e50
        | exact resolve b3e50 b3e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e45 b3e50
      have b3e74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 X0 X1
           have i₂ := b3e14 (σ X0) (σ X1)
           grind)
        | exact superpose b3e14 b3e15
        | (have j1 := b3e14 (σ X0) (σ X1)
           grind)
        | exact resolve b3e15 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e79 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e74 X0 X1
           have i₂ := b3e55 X1
           grind)
        | exact superpose b3e55 b3e74
        | (have j0 := b3e74 X0 X1
           grind)
        | exact resolve b3e74 b3e55
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e74
      have b3e1901 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e79 x y
           grind)
        | exact superpose b3e79 b3e16
        | (have j1 := b3e79 x y
           grind)
        | exact resolve b3e16 b3e79
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e79
      have b3e49960 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b3e1901
           have i₂ := b3e14 x y
           grind)
        | exact superpose b3e14 b3e1901
        | (have j1 := b3e14 x y
           grind)
        | exact resolve b3e1901 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1901
      have b3e49966 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
      clear b3e49960
      have b3e49967 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
        first
        | (have r₁ := b3e49966
           have r₂ := b3e17
           grind)
        | exact resolve b3e49966 b3e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e49966
      have b3e49972 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b3e18
           have i₂ := b3e49967
           grind)
        | exact superpose b3e49967 b3e18
        | exact resolve b3e18 b3e49967
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e49967
      have b3e50082 : False := by grind
      exact b3e50082

/-- `Equation3320`: `x ◇ y = x ◇ (y ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_x_x_pyx_pxy_Equation3320 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3320 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3320.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e36 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1 X0 (M.op X0 x)
           have i₂ := b0e11 X0 X0 x
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e47 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e36 x X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e36
        | exact resolve b0e36 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e48 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e36 (σ x) X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e36
        | exact resolve b0e36 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36
      have b0e153 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e48 (σ x)
           grind)
        | exact superpose b0e48 b0e18
        | exact resolve b0e18 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48
      have b0e154 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e153
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e153
        | exact resolve b0e153 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e153
      have b0e159 : (σ y) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e154
           have i₂ := b0e47 x
           grind)
        | exact superpose b0e47 b0e154
        | exact resolve b0e154 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47 b0e154
      have b0e160 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e159
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e159
        | exact resolve b0e159 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e159
      have b0e161 : False := by grind
      exact b0e161
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X1 (τ X0)
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e18
          | exact resolve b1e18 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X0 X1
             have i₂ := b1e17 (σ X0) (σ X1)
             grind)
          | exact superpose b1e17 b1e18
          | (have j1 := b1e17 (σ X0) (σ X1)
             grind)
          | exact resolve b1e18 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e145 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e13 (k X0 (τ X1))
             have i₂ := b1e26 X1 X0
             grind)
          | exact superpose b1e26 b1e13
          | exact resolve b1e13 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e259 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b1e145
        have b1e273 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e259 X0
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e259
          | exact resolve b1e259 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e259
        have b1e319 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e65 x x
             grind)
          | exact superpose b1e65 b1e21
          | (have j1 := b1e65 x x
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e65 x y
             grind)
          | exact resolve b1e21 b1e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e65
        have b1e361 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b1e319
        have b1e1790 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e361
             have i₂ := b1e17 x x
             grind)
          | exact superpose b1e17 b1e361
          | (have j1 := b1e17 (σ x) (σ x)
             grind)
          | exact resolve b1e361 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e361
        have b1e1791 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b1e1790
        have b1e1792 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e1791
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1791
          | exact resolve b1e1791 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1791
        have b1e1793 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b1e1792
        have b1e1799 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b1e1793
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1793
          | exact resolve b1e1793 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1793
        have b1e1809 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b1e273 x
             have i₂ := b1e1799
             grind)
          | exact superpose b1e1799 b1e273
          | exact resolve b1e273 b1e1799
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e273 b1e1799
        have b1e1824 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b1e1809
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e1809
          | exact resolve b1e1809 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1809
        have b1e1942 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b1e17 x x
             have i₂ := b1e1824
             grind)
          | exact superpose b1e1824 b1e17
          | (have j0 := b1e17 x x
             grind)
          | exact resolve b1e17 b1e1824
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1824
        have b1e1943 : x = (M.op x x) ∨ x = y := by grind
        clear b1e1942
        have b1e1952 : x = y ∨ x = y := by
          first
          | (have i₁ := b1e1943
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1943
          | exact resolve b1e1943 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1943
        have b1e1953 : x = y := by grind
        clear b1e1952
        have b1e2446 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e1953
             grind)
          | exact superpose b1e1953 b1e22
          | exact resolve b1e22 b1e1953
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2680 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e2446
             grind)
          | exact superpose b1e2446 b1e21
          | exact resolve b1e21 b1e2446
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2446
        have b1e2699 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e2680
             have i₂ := b1e1953
             grind)
          | exact superpose b1e1953 b1e2680
          | exact resolve b1e2680 b1e1953
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1953 b1e2680
        have b1e2700 : False := by grind
        exact b1e2700
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : x = (k x y) := by grind
        have b2e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e18
          | exact resolve b2e18 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e29 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 X0 (M.op X0 x)
             have i₂ := b2e12 X0 X0 x
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e39 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b2e29 x X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e29
          | exact resolve b2e29 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29
        have b2e59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e17 (σ X0) (σ X1)
             grind)
          | exact superpose b2e17 b2e18
          | (have j1 := b2e17 (σ X0) (σ X1)
             grind)
          | exact resolve b2e18 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e67 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e17 (σ x) X0
             grind)
          | (have i₁ := b2e21
             have i₂ := b2e17 X0 (M.op (σ x) (σ x))
             grind)
          | exact superpose b2e17 b2e21
          | (have j1 := b2e17 (σ x) X0
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | exact resolve b2e21 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e108 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k X0 (τ X1))
             have i₂ := b2e26 X1 X0
             grind)
          | exact superpose b2e26 b2e13
          | exact resolve b2e13 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26
        have b2e179 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e67 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e67
        have b2e180 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e179
             have r₂ := b2e22
             grind)
          | exact resolve b2e179 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e179
        have b2e181 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e180
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e180
          | exact resolve b2e180 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e180
        have b2e182 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e181
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e181
          | exact resolve b2e181 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e181
        have b2e183 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e182
             grind)
          | exact superpose b2e182 b2e19
          | exact resolve b2e19 b2e182
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e182
        have b2e188 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e183
             have i₂ := b2e39 x
             grind)
          | exact superpose b2e39 b2e183
          | exact resolve b2e183 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39 b2e183
        have b2e189 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e188
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e188
          | exact resolve b2e188 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e188
        have b2e247 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e59 x x
             grind)
          | exact superpose b2e59 b2e21
          | (have j1 := b2e59 x x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e59 x y
             grind)
          | exact resolve b2e21 b2e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e59
        have b2e287 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e247
        have b2e328 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b2e108
        have b2e342 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e328 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e328
          | exact resolve b2e328 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e328
        have b2e1551 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e287
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e287
          | (have j1 := b2e17 (σ x) (σ x)
             grind)
          | exact resolve b2e287 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e287
        have b2e1552 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e1551
        have b2e1553 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e1552
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1552
          | exact resolve b2e1552 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1552
        have b2e1554 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e1553
        have b2e1560 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e1554
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1554
          | exact resolve b2e1554 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1554
        have b2e1570 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b2e342 x
             have i₂ := b2e1560
             grind)
          | exact superpose b2e1560 b2e342
          | exact resolve b2e342 b2e1560
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e342 b2e1560
        have b2e1585 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e1570
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e1570
          | exact resolve b2e1570 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1570
        have b2e1614 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b2e17 x x
             have i₂ := b2e1585
             grind)
          | exact superpose b2e1585 b2e17
          | (have j0 := b2e17 x x
             grind)
          | exact resolve b2e17 b2e1585
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1585
        have b2e1615 : x = (M.op x x) ∨ x = y := by grind
        clear b2e1614
        have b2e1624 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e1615
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1615
          | exact resolve b2e1615 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1615
        have b2e1625 : x = y := by grind
        clear b2e1624
        have b2e1725 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e189
             have i₂ := b2e1625
             grind)
          | exact superpose b2e1625 b2e189
          | exact resolve b2e189 b2e1625
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e189 b2e1625
        have b2e1727 : False := by grind
        exact b2e1727
  · rcases eq_or_ne (M.op y x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e21 : x = (M.op y x) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e40 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y x)) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 y x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e43 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X1 X0 (M.op X0 x)
             have i₂ := b3e12 X0 X0 x
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e45 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b3e40 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e40
          | exact resolve b3e40 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40
        have b3e63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e18 X0 X1
             have i₂ := b3e17 (σ X0) (σ X1)
             grind)
          | exact superpose b3e17 b3e18
          | (have j1 := b3e17 (σ X0) (σ X1)
             grind)
          | exact resolve b3e18 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e79 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e43 (σ x) X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e43
          | exact resolve b3e43 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43
        have b3e106 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e79 (σ x)
             grind)
          | exact superpose b3e79 b3e19
          | exact resolve b3e19 b3e79
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e79
        have b3e115 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b3e106
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e106
          | exact resolve b3e106 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e106
        have b3e117 : (σ y) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e115
             have i₂ := b3e45 x
             grind)
          | exact superpose b3e45 b3e115
          | exact resolve b3e115 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45 b3e115
        have b3e330 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e63 x x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e63
          | exact resolve b3e63 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e63
        have b3e380 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b3e330
        have b3e821 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e380
             have i₂ := b3e17 x x
             grind)
          | exact superpose b3e17 b3e380
          | (have j1 := b3e17 x x
             grind)
          | exact resolve b3e380 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e833 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
        clear b3e821
        have b3e845 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b3e833
             have r₂ := b3e117
             grind)
          | exact resolve b3e833 b3e117
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e117 b3e833
        have b3e918 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b3e845
        have b3e1070 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e380
             have i₂ := b3e918
             grind)
          | exact superpose b3e918 b3e380
          | exact resolve b3e380 b3e918
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e380 b3e918
        have b3e1077 : (σ x) = (σ y) := by grind
        clear b3e1070
        have b3e1137 : y = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 y
             have i₂ := b3e1077
             grind)
          | exact superpose b3e1077 b3e13
          | exact resolve b3e13 b3e1077
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1164 : x = y := by
          first
          | (have i₁ := b3e1137
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e1137
          | exact resolve b3e1137 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1137
        have b3e1181 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e1164
             grind)
          | exact superpose b3e1164 b3e19
          | exact resolve b3e19 b3e1164
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1182 : x = (M.op x x) := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e1164
             grind)
          | exact superpose b3e1164 b3e21
          | exact resolve b3e21 b3e1164
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1164
        have b3e1189 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e1181
             have i₂ := b3e1182
             grind)
          | exact superpose b3e1182 b3e1181
          | exact resolve b3e1181 b3e1182
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1181 b3e1182
        have b3e1190 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e1189
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e1189
          | exact resolve b3e1189 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1189
        have b3e1191 : False := by grind
        exact b3e1191
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op y x) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e19
            | exact resolve b4e19 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e28 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y x)) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e29 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) (σ x))) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 (σ y) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e33 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e29 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e29
            | exact resolve b4e29 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29
          have b4e34 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b4e28 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e28
            | exact resolve b4e28 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28
          have b4e54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X0 X1
               have i₂ := b4e18 (σ X0) (σ X1)
               grind)
            | exact superpose b4e18 b4e19
            | (have j1 := b4e18 (σ X0) (σ X1)
               grind)
            | exact resolve b4e19 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e86 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e33 (σ x)
               grind)
            | exact superpose b4e33 b4e20
            | exact resolve b4e20 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33
          have b4e96 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e86
               have i₂ := b4e34 x
               grind)
            | exact superpose b4e34 b4e86
            | exact resolve b4e86 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34 b4e86
          have b4e115 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k X0 (τ X1))
               have i₂ := b4e27 X1 X0
               grind)
            | exact superpose b4e27 b4e14
            | exact resolve b4e14 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e197 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
            intro X0
            grind
          clear b4e115
          have b4e211 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e197 X0
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e197
            | exact resolve b4e197 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e197
          have b4e251 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e96
               have i₂ := b4e54 x x
               grind)
            | exact superpose b4e54 b4e96
            | (have j1 := b4e54 x x
               grind)
            | (have r₁ := b4e96
               have r₂ := b4e54 x (M.op x x)
               grind)
            | exact resolve b4e96 b4e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e286 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e54 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54
          have b4e287 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e286 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e286
          have b4e296 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b4e251
          have b4e1333 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e287 (τ X0)
               have i₂ := b4e27 X0 (τ X0)
               grind)
            | exact superpose b4e27 b4e287
            | (have j0 := b4e287 (τ X0)
               grind)
            | exact resolve b4e287 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27
          have b4e1337 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e1333 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e1333
            | (have j0 := b4e1333 X0
               grind)
            | exact resolve b4e1333 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1333
          have b4e1341 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e1337 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e1337
            | (have j0 := b4e1337 X0
               grind)
            | exact resolve b4e1337 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1337
          have b4e15207 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e296
               have i₂ := b4e18 x x
               grind)
            | exact superpose b4e18 b4e296
            | (have j1 := b4e18 (σ x) (σ x)
               grind)
            | exact resolve b4e296 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e296
          have b4e15209 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
          clear b4e15207
          have b4e15210 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
          clear b4e15209
          have b4e15582 : x = (k x (τ (σ x))) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e211 x
               have i₂ := b4e15210
               grind)
            | exact superpose b4e15210 b4e211
            | exact resolve b4e211 b4e15210
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e211 b4e15210
          have b4e15622 : x = (k x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e15582
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e15582
            | exact resolve b4e15582 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e15582
          have b4e15623 : x = (M.op x x) := by
            first
            | (have j1 := b4e1341 x
               grind)
            | (have r₁ := b4e15622
               have r₂ := b4e1341 x
               grind)
            | exact resolve b4e15622 b4e1341
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1341 b4e15622
          have b4e15992 : x = (k x x) := by grind
          have b4e16637 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e287 x
               have i₂ := b4e15992
               grind)
            | exact superpose b4e15992 b4e287
            | (have j0 := b4e287 x
               grind)
            | exact resolve b4e287 b4e15992
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e287 b4e15992
          have b4e16656 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b4e16637
          have b4e17196 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e96
               have i₂ := b4e16656
               grind)
            | exact superpose b4e16656 b4e96
            | exact resolve b4e96 b4e16656
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e96 b4e16656
          have b4e17243 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e17196
               have i₂ := b4e15623
               grind)
            | exact superpose b4e15623 b4e17196
            | exact resolve b4e17196 b4e15623
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e15623 b4e17196
          have b4e17244 : False := by grind
          exact b4e17244
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : y ≠ (M.op x x) := by grind
          have b5e22 : x = (M.op y x) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e26 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 (τ X0) X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e19
            | exact resolve b5e19 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X1 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e19
            | exact resolve b5e19 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e28 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y x)) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e30 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 X0 (M.op X0 x)
               have i₂ := b5e13 X0 X0 x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e32 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b5e28 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e28
            | exact resolve b5e28 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28
          have b5e36 : x ≠ x ∨ y = (M.op x x) ∨ x = (k x y) := by
            first
            | (have i₁ := b5e17 x y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e17
            | (have j0 := b5e17 x y
               grind)
            | (have r₁ := b5e17 x y
               have r₂ := b5e22
               grind)
            | exact resolve b5e17 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e39 : y = (M.op x x) ∨ x = (k x y) := by grind
          clear b5e36
          have b5e42 : x = (k x y) := by
            first
            | (have r₁ := b5e39
               have r₂ := b5e21
               grind)
            | exact resolve b5e39 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39
          have b5e48 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X0 X1
               have i₂ := b5e18 (σ X0) (σ X1)
               grind)
            | exact superpose b5e18 b5e19
            | (have j1 := b5e18 (σ X0) (σ X1)
               grind)
            | exact resolve b5e19 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e54 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e23
               have i₂ := b5e18 (σ x) X0
               grind)
            | (have i₁ := b5e23
               have i₂ := b5e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b5e18 b5e23
            | (have j1 := b5e18 (σ x) X0
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | exact resolve b5e23 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e92 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k X0 (τ X1))
               have i₂ := b5e27 X1 X0
               grind)
            | exact superpose b5e27 b5e14
            | exact resolve b5e14 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27
          have b5e167 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b5e54 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e54
          have b5e168 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e167
               have r₂ := b5e24
               grind)
            | exact resolve b5e167 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e167
          have b5e169 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e168
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e168
            | exact resolve b5e168 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e168
          have b5e170 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e169
               have i₂ := b5e42
               grind)
            | exact superpose b5e42 b5e169
            | exact resolve b5e169 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42 b5e169
          have b5e171 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e170
               grind)
            | exact superpose b5e170 b5e20
            | exact resolve b5e20 b5e170
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e176 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e171
               have i₂ := b5e32 x
               grind)
            | exact superpose b5e32 b5e171
            | exact resolve b5e171 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e171
          have b5e255 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e17 (σ X0) (σ X1)
               have i₂ := b5e48 X0 X1
               grind)
            | exact superpose b5e48 b5e17
            | (have j0 := b5e17 (σ X0) (σ X1)
               have j1 := b5e48 X0 X1
               grind)
            | (have r₁ := b5e17 (σ X1) (σ X1)
               have r₂ := b5e48 X1 X1
               grind)
            | (have r₁ := b5e17 (σ X0) (σ X1)
               have r₂ := b5e48 X0 X1
               grind)
            | exact resolve b5e17 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48
          have b5e261 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e255 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e255
          have b5e262 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e261 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e261
          have b5e274 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e262 X0 X1
               have i₂ := b5e19 X0 X1
               grind)
            | exact superpose b5e19 b5e262
            | (have j0 := b5e262 X0 X1
               grind)
            | exact resolve b5e262 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e262
          have b5e4737 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            grind
          clear b5e274
          have b5e4774 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e4737 X0 X1
               have i₂ := b5e19 X1 X0
               grind)
            | exact superpose b5e19 b5e4737
            | (have j0 := b5e4737 X0 X1
               grind)
            | exact resolve b5e4737 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4737
          have b5e4775 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e4774 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4774
          have b5e7326 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e4775 X0 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e4775
            | exact resolve b5e4775 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e7424 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e7326 X0 X1
               have i₂ := b5e26 X0 X1
               grind)
            | exact superpose b5e26 b5e7326
            | (have j0 := b5e7326 X0 X1
               grind)
            | exact resolve b5e7326 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7326
          have b5e7429 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e7424 X0 X1
               have i₂ := b5e26 X0 X1
               grind)
            | exact superpose b5e26 b5e7424
            | (have j0 := b5e7424 X0 X1
               grind)
            | exact resolve b5e7424 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e7424
          have b5e11430 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e7429 X0 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e7429
            | exact resolve b5e7429 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7429
          have b5e12323 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e11430 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11430
          have b5e13123 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 (M.op X1 X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e12323 X0 (M.op X1 X1)
               have i₂ := b5e30 X1 X0
               grind)
            | exact superpose b5e30 b5e12323
            | (have j0 := b5e12323 X0 X1
               grind)
            | exact resolve b5e12323 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e12323
          have b5e14806 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (M.op (σ y) (σ y))) := by
            first
            | (have i₁ := b5e13123 (σ x) (σ y)
               have i₂ := b5e170
               grind)
            | exact superpose b5e170 b5e13123
            | (have j0 := b5e13123 (σ x) (σ y)
               grind)
            | (have r₁ := b5e13123 (σ x) (σ y)
               have r₂ := b5e170
               grind)
            | exact resolve b5e13123 b5e170
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e13123
          have b5e14836 : (σ x) = (k (σ x) (M.op (σ y) (σ y))) := by grind
          clear b5e14806
          have b5e15330 : (k x (τ (M.op (σ y) (σ y)))) = (τ (σ x)) := by
            first
            | (have i₁ := b5e92 x (M.op (σ y) (σ y))
               have i₂ := b5e14836
               grind)
            | exact superpose b5e14836 b5e92
            | exact resolve b5e92 b5e14836
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e92 b5e14836
          have b5e15355 : x = (k x (τ (M.op (σ y) (σ y)))) := by
            first
            | (have i₁ := b5e15330
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e15330
            | exact resolve b5e15330 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e15330
          have b5e16135 : x = (k x (τ (σ (k y y)))) ∨ (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b5e15355
               have i₂ := b5e4775 y y
               grind)
            | exact superpose b5e4775 b5e15355
            | (have j1 := b5e4775 y y
               grind)
            | exact resolve b5e15355 b5e4775
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4775 b5e15355
          have b5e16171 : x = (k x (k y y)) ∨ (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b5e16135
               have i₂ := b5e14 (k y y)
               grind)
            | exact superpose b5e14 b5e16135
            | exact resolve b5e16135 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16135
          have b5e23078 : x = (k x (M.op y y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e16171
               have i₂ := b5e18 y y
               grind)
            | exact superpose b5e18 b5e16171
            | (have j1 := b5e18 y y
               grind)
            | exact resolve b5e16171 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16171
          have b5e23099 : x = (k x (M.op y y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
          clear b5e23078
          have b5e23105 : x = (k x (M.op y x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e23099
               have i₂ := b5e32 y
               grind)
            | exact superpose b5e32 b5e23099
            | exact resolve b5e23099 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e23099
          have b5e23111 : x = (k x x) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e23105
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e23105
            | exact resolve b5e23105 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e23105
          have b5e23117 : (σ y) = (σ (M.op y x)) ∨ x = (k x x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e23111
               have i₂ := b5e32 y
               grind)
            | exact superpose b5e32 b5e23111
            | exact resolve b5e23111 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e23111
          have b5e23123 : (σ x) = (σ y) ∨ x = (k x x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e23117
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e23117
            | exact resolve b5e23117 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e23117
          have b5e23128 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (k x x) := by
            first
            | (have i₁ := b5e23123
               have i₂ := b5e32 y
               grind)
            | exact superpose b5e32 b5e23123
            | exact resolve b5e23123 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32 b5e23123
          have b5e23131 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
            first
            | (have i₁ := b5e23128
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e23128
            | exact resolve b5e23128 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e23128
          have b5e24454 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
            first
            | (have i₁ := b5e18 x x
               have i₂ := b5e23131
               grind)
            | exact superpose b5e23131 b5e18
            | (have j0 := b5e18 x x
               grind)
            | exact resolve b5e18 b5e23131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e23131
          have b5e24463 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
          clear b5e24454
          have b5e24749 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
            first
            | (have i₁ := b5e176
               have i₂ := b5e24463
               grind)
            | exact superpose b5e24463 b5e176
            | exact resolve b5e176 b5e24463
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e176 b5e24463
          have b5e24797 : (σ x) = (σ y) ∨ x = y := by grind
          clear b5e24749
          have b5e25062 : y = (τ (σ x)) ∨ x = y := by
            first
            | (have i₁ := b5e14 y
               have i₂ := b5e24797
               grind)
            | exact superpose b5e24797 b5e14
            | exact resolve b5e14 b5e24797
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e24797
          have b5e25183 : x = y ∨ x = y := by
            first
            | (have i₁ := b5e25062
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e25062
            | exact resolve b5e25062 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25062
          have b5e25184 : x = y := by grind
          clear b5e25183
          have b5e25191 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e25184
               grind)
            | exact superpose b5e25184 b5e24
            | exact resolve b5e24 b5e25184
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e25196 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e170
               have i₂ := b5e25184
               grind)
            | exact superpose b5e25184 b5e170
            | exact resolve b5e170 b5e25184
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e170 b5e25184
          have b5e25218 : False := by grind
          exact b5e25218
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : x ≠ (M.op y x) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e24 : (σ x) = (k (σ x) (σ y)) := by grind
        have b6e25 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b6e24
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e24
          | exact resolve b6e24 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24
        have b6e42 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X1 X0 (M.op X0 x)
             have i₂ := b6e12 X0 X0 x
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e44 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e42 (σ x) X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e42
          | exact resolve b6e42 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42
        have b6e57 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e44 (σ x)
             grind)
          | exact superpose b6e44 b6e19
          | exact resolve b6e19 b6e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e44
        have b6e64 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e57
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e57
          | exact resolve b6e57 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e57
        have b6e72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X0 X1
             have i₂ := b6e17 (σ X0) (σ X1)
             grind)
          | exact superpose b6e17 b6e18
          | (have j1 := b6e17 (σ X0) (σ X1)
             grind)
          | exact resolve b6e18 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e75 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
          first
          | (have i₁ := b6e25
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e25
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e25 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e87 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
          first
          | (have r₁ := b6e75
             have r₂ := b6e20
             grind)
          | exact resolve b6e75 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e75
        have b6e93 : (σ (M.op x y)) = (σ x) := by
          first
          | (have r₁ := b6e87
             have r₂ := b6e21
             grind)
          | exact resolve b6e87 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e87
        have b6e146 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b6e64
             have i₂ := b6e93
             grind)
          | exact superpose b6e93 b6e64
          | exact resolve b6e64 b6e93
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64 b6e93
        have b6e312 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e72 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e72
          | exact resolve b6e72 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e72
        have b6e362 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) := by grind
        clear b6e312
        have b6e380 : (σ y) = (σ (k x x)) := by
          first
          | (have r₁ := b6e362
             have r₂ := b6e146
             grind)
          | exact resolve b6e362 b6e146
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e362
        have b6e417 : (k x x) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e380
             grind)
          | exact superpose b6e380 b6e13
          | exact resolve b6e13 b6e380
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e437 : y = (k x x) := by
          first
          | (have i₁ := b6e417
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e417
          | exact resolve b6e417 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e417
        have b6e497 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e437
             grind)
          | exact superpose b6e437 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e437
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e437
        have b6e498 : y = (M.op x x) ∨ x = (M.op x x) := by grind
        clear b6e497
        have b6e500 : x = (M.op x x) := by
          first
          | (have r₁ := b6e498
             have r₂ := b6e20
             grind)
          | exact resolve b6e498 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e498
        have b6e547 : x = (k x x) := by grind
        clear b6e500
        have b6e736 : (σ x) = (σ y) := by
          first
          | (have i₁ := b6e380
             have i₂ := b6e547
             grind)
          | exact superpose b6e547 b6e380
          | exact resolve b6e380 b6e547
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e380 b6e547
        have b6e747 : False := by grind
        exact b6e747
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : x ≠ (M.op y x) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e28 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) (σ x))) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ y) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e30 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X1 X0 (M.op X0 x)
               have i₂ := b7e13 X0 X0 x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e32 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e28 X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e28
            | exact resolve b7e28 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28
          have b7e36 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op X0 X0) X0)) := by
            intro X0
            grind
          clear b7e30
          have b7e40 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e17 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e17
            | (have j0 := b7e17 (σ x) (σ y)
               grind)
            | (have r₁ := b7e17 (σ x) (σ y)
               have r₂ := b7e24
               grind)
            | exact resolve b7e17 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e43 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e40
          have b7e46 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e43
               have r₂ := b7e23
               grind)
            | exact resolve b7e43 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e43
          have b7e47 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e46
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e46
            | exact resolve b7e46 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e50 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e47
               grind)
            | exact superpose b7e47 b7e14
            | exact resolve b7e14 b7e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e51 : x = (k x y) := by
            first
            | (have i₁ := b7e50
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e50
            | exact resolve b7e50 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e19 X0 X1
               have i₂ := b7e18 (σ X0) (σ X1)
               grind)
            | exact superpose b7e18 b7e19
            | (have j1 := b7e18 (σ X0) (σ X1)
               grind)
            | exact resolve b7e19 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e59 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b7e47
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e47
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e47 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
          have b7e69 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
            first
            | (have r₁ := b7e59
               have r₂ := b7e21
               grind)
            | exact resolve b7e59 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e59
          have b7e72 : (σ (M.op x y)) = (σ x) := by
            first
            | (have r₁ := b7e69
               have r₂ := b7e22
               grind)
            | exact resolve b7e69 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69
          have b7e74 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e51
               grind)
            | exact superpose b7e51 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51
          have b7e75 : x = (M.op x y) ∨ x = (M.op y x) := by
            first
            | (have r₁ := b7e74
               have r₂ := b7e21
               grind)
            | exact resolve b7e74 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e74
          have b7e77 : x = (M.op x y) := by
            first
            | (have r₁ := b7e75
               have r₂ := b7e22
               grind)
            | exact resolve b7e75 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e75
          have b7e80 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e32 (σ x)
               grind)
            | exact superpose b7e32 b7e20
            | exact resolve b7e20 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e90 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e80
               have i₂ := b7e72
               grind)
            | exact superpose b7e72 b7e80
            | exact resolve b7e80 b7e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72 b7e80
          have b7e288 : ∀ X0 : G, (σ y) = (M.op (σ X0) (σ x)) ∨ (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e32 (σ X0)
               have i₂ := b7e58 y X0
               grind)
            | exact superpose b7e58 b7e32
            | (have j1 := b7e58 y X0
               grind)
            | exact resolve b7e32 b7e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e294 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e58 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58
          have b7e295 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e294 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e294
          have b7e312 : ∀ X0 : G, (σ X0) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ X0) (σ x)) ∨ (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e288 X0
               have i₂ := b7e32 (σ y)
               grind)
            | exact superpose b7e32 b7e288
            | (have j0 := b7e288 X0
               grind)
            | exact resolve b7e288 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e288
          have b7e351 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (σ x) := by
            intro X0
            first
            | (have i₁ := b7e312 X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e312
            | (have j0 := b7e312 X0
               grind)
            | exact resolve b7e312 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e312
          have b7e2442 : (M.op (σ y) (σ x)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e32 (σ y)
               have i₂ := b7e351 y
               grind)
            | exact superpose b7e351 b7e32
            | (have j1 := b7e351 y
               grind)
            | exact resolve b7e32 b7e351
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32 b7e351
          have b7e2505 : (σ x) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e2442
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e2442
            | exact resolve b7e2442 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2442
          have b7e2544 : (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e2505
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e2505
            | exact resolve b7e2505 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2505
          have b7e2545 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
          clear b7e2544
          have b7e2580 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e2545
               grind)
            | exact superpose b7e2545 b7e14
            | exact resolve b7e14 b7e2545
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e2618 : x = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e2580
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e2580
            | exact resolve b7e2580 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2580
          have b7e2764 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e18 y y
               have i₂ := b7e2618
               grind)
            | exact superpose b7e2618 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e2618
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2618
          have b7e2765 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b7e2764
          have b7e7257 : y = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b7e2765
          have b7e7877 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e2545
               have i₂ := b7e7257
               grind)
            | exact superpose b7e7257 b7e2545
            | exact resolve b7e2545 b7e7257
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2545 b7e7257
          have b7e7898 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b7e7877
          have b7e8292 : x = (k x (M.op x y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e36 y
               have i₂ := b7e7898
               grind)
            | exact superpose b7e7898 b7e36
            | exact resolve b7e36 b7e7898
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36 b7e7898
          have b7e8325 : x = (k x x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e8292
               have i₂ := b7e77
               grind)
            | exact superpose b7e77 b7e8292
            | exact resolve b7e8292 b7e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77 b7e8292
          have b7e8899 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e295 x
               have i₂ := b7e8325
               grind)
            | exact superpose b7e8325 b7e295
            | (have j0 := b7e295 x
               grind)
            | exact resolve b7e295 b7e8325
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e295 b7e8325
          have b7e8918 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
          clear b7e8899
          have b7e8924 : (σ x) = (σ y) := by
            first
            | (have r₁ := b7e8918
               have r₂ := b7e90
               grind)
            | exact resolve b7e8918 b7e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e8918
          have b7e9095 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e8924
               grind)
            | exact superpose b7e8924 b7e24
            | exact resolve b7e24 b7e8924
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e8924
          have b7e9191 : False := by grind
          exact b7e9191
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x x) := by grind
          have b8e22 : x ≠ (M.op y x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e60 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 (σ x) X0
               grind)
            | (have i₁ := b8e23
               have i₂ := b8e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b8e18 b8e23
            | (have j1 := b8e18 (σ x) X0
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e117 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b8e60 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60
          have b8e118 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e117
               have r₂ := b8e24
               grind)
            | exact resolve b8e117 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e117
          have b8e119 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e118
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e118
            | exact resolve b8e118 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e118
          have b8e156 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e119
               grind)
            | exact superpose b8e119 b8e20
            | exact resolve b8e20 b8e119
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e119
          have b8e271 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e156
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e156
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e156 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e156
          have b8e272 : y = (M.op x x) ∨ x = (M.op y x) := by grind
          clear b8e271
          have b8e274 : x = (M.op y x) := by
            first
            | (have r₁ := b8e272
               have r₂ := b8e21
               grind)
            | exact resolve b8e272 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e272
          have b8e276 : False := by grind
          exact b8e276

/-- `Equation3320`: `x ◇ y = x ◇ (y ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_x_x_pyy_pxy_Equation3320 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3320 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3320.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e36 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1 X0 (M.op X0 x)
           have i₂ := b0e11 X0 X0 x
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e47 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e36 x X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e36
        | exact resolve b0e36 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e48 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e36 (σ x) X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e36
        | exact resolve b0e36 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36
      have b0e153 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e48 (σ x)
           grind)
        | exact superpose b0e48 b0e18
        | exact resolve b0e18 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48
      have b0e154 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e153
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e153
        | exact resolve b0e153 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e153
      have b0e159 : (σ y) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e154
           have i₂ := b0e47 x
           grind)
        | exact superpose b0e47 b0e154
        | exact resolve b0e154 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47 b0e154
      have b0e160 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e159
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e159
        | exact resolve b0e159 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e159
      have b0e161 : False := by grind
      exact b0e161
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X1 (τ X0)
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e18
          | exact resolve b1e18 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X0 X1
             have i₂ := b1e17 (σ X0) (σ X1)
             grind)
          | exact superpose b1e17 b1e18
          | (have j1 := b1e17 (σ X0) (σ X1)
             grind)
          | exact resolve b1e18 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e147 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e13 (k X0 (τ X1))
             have i₂ := b1e26 X1 X0
             grind)
          | exact superpose b1e26 b1e13
          | exact resolve b1e13 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e261 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b1e147
        have b1e275 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e261 X0
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e261
          | exact resolve b1e261 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e261
        have b1e321 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e67 x x
             grind)
          | exact superpose b1e67 b1e21
          | (have j1 := b1e67 x x
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e67 x y
             grind)
          | exact resolve b1e21 b1e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e67
        have b1e363 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b1e321
        have b1e1784 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e363
             have i₂ := b1e17 x x
             grind)
          | exact superpose b1e17 b1e363
          | (have j1 := b1e17 (σ x) (σ x)
             grind)
          | exact resolve b1e363 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e363
        have b1e1785 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b1e1784
        have b1e1786 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e1785
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1785
          | exact resolve b1e1785 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1785
        have b1e1787 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b1e1786
        have b1e1793 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b1e1787
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1787
          | exact resolve b1e1787 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1787
        have b1e1803 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b1e275 x
             have i₂ := b1e1793
             grind)
          | exact superpose b1e1793 b1e275
          | exact resolve b1e275 b1e1793
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e275 b1e1793
        have b1e1818 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b1e1803
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e1803
          | exact resolve b1e1803 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1803
        have b1e1936 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b1e17 x x
             have i₂ := b1e1818
             grind)
          | exact superpose b1e1818 b1e17
          | (have j0 := b1e17 x x
             grind)
          | exact resolve b1e17 b1e1818
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1818
        have b1e1937 : x = (M.op x x) ∨ x = y := by grind
        clear b1e1936
        have b1e1946 : x = y ∨ x = y := by
          first
          | (have i₁ := b1e1937
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1937
          | exact resolve b1e1937 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1937
        have b1e1947 : x = y := by grind
        clear b1e1946
        have b1e2440 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e1947
             grind)
          | exact superpose b1e1947 b1e22
          | exact resolve b1e22 b1e1947
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2675 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e2440
             grind)
          | exact superpose b1e2440 b1e21
          | exact resolve b1e21 b1e2440
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2440
        have b1e2694 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e2675
             have i₂ := b1e1947
             grind)
          | exact superpose b1e1947 b1e2675
          | exact resolve b1e2675 b1e1947
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1947 b1e2675
        have b1e2695 : False := by grind
        exact b1e2695
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : x = (k x y) := by grind
        have b2e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e18
          | exact resolve b2e18 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e29 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 X0 (M.op X0 x)
             have i₂ := b2e12 X0 X0 x
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e39 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b2e29 x X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e29
          | exact resolve b2e29 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29
        have b2e59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e17 (σ X0) (σ X1)
             grind)
          | exact superpose b2e17 b2e18
          | (have j1 := b2e17 (σ X0) (σ X1)
             grind)
          | exact resolve b2e18 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e67 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e17 (σ x) X0
             grind)
          | (have i₁ := b2e21
             have i₂ := b2e17 X0 (M.op (σ x) (σ x))
             grind)
          | exact superpose b2e17 b2e21
          | (have j1 := b2e17 (σ x) X0
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | exact resolve b2e21 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e108 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k X0 (τ X1))
             have i₂ := b2e26 X1 X0
             grind)
          | exact superpose b2e26 b2e13
          | exact resolve b2e13 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26
        have b2e179 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e67 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e67
        have b2e180 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e179
             have r₂ := b2e22
             grind)
          | exact resolve b2e179 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e179
        have b2e181 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e180
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e180
          | exact resolve b2e180 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e180
        have b2e182 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e181
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e181
          | exact resolve b2e181 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e181
        have b2e183 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e182
             grind)
          | exact superpose b2e182 b2e19
          | exact resolve b2e19 b2e182
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e182
        have b2e188 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e183
             have i₂ := b2e39 x
             grind)
          | exact superpose b2e39 b2e183
          | exact resolve b2e183 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39 b2e183
        have b2e189 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e188
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e188
          | exact resolve b2e188 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e188
        have b2e247 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e59 x x
             grind)
          | exact superpose b2e59 b2e21
          | (have j1 := b2e59 x x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e59 x y
             grind)
          | exact resolve b2e21 b2e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e59
        have b2e287 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e247
        have b2e328 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b2e108
        have b2e342 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e328 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e328
          | exact resolve b2e328 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e328
        have b2e1545 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e287
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e287
          | (have j1 := b2e17 (σ x) (σ x)
             grind)
          | exact resolve b2e287 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e287
        have b2e1546 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e1545
        have b2e1547 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e1546
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1546
          | exact resolve b2e1546 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1546
        have b2e1548 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e1547
        have b2e1554 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e1548
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1548
          | exact resolve b2e1548 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1548
        have b2e1564 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b2e342 x
             have i₂ := b2e1554
             grind)
          | exact superpose b2e1554 b2e342
          | exact resolve b2e342 b2e1554
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e342 b2e1554
        have b2e1579 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e1564
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e1564
          | exact resolve b2e1564 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1564
        have b2e1608 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b2e17 x x
             have i₂ := b2e1579
             grind)
          | exact superpose b2e1579 b2e17
          | (have j0 := b2e17 x x
             grind)
          | exact resolve b2e17 b2e1579
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1579
        have b2e1609 : x = (M.op x x) ∨ x = y := by grind
        clear b2e1608
        have b2e1618 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e1609
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1609
          | exact resolve b2e1609 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1609
        have b2e1619 : x = y := by grind
        clear b2e1618
        have b2e1719 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e189
             have i₂ := b2e1619
             grind)
          | exact superpose b2e1619 b2e189
          | exact resolve b2e189 b2e1619
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e189 b2e1619
        have b2e1721 : False := by grind
        exact b2e1721
  · rcases eq_or_ne (M.op y x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e21 : x = (M.op y x) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e40 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y x)) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 y x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e43 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X1 X0 (M.op X0 x)
             have i₂ := b3e12 X0 X0 x
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e45 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b3e40 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e40
          | exact resolve b3e40 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40
        have b3e66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e18 X0 X1
             have i₂ := b3e17 (σ X0) (σ X1)
             grind)
          | exact superpose b3e17 b3e18
          | (have j1 := b3e17 (σ X0) (σ X1)
             grind)
          | exact resolve b3e18 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e82 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e43 (σ x) X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e43
          | exact resolve b3e43 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43
        have b3e109 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e82 (σ x)
             grind)
          | exact superpose b3e82 b3e19
          | exact resolve b3e19 b3e82
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e82
        have b3e118 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b3e109
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e109
          | exact resolve b3e109 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e109
        have b3e120 : (σ y) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e118
             have i₂ := b3e45 x
             grind)
          | exact superpose b3e45 b3e118
          | exact resolve b3e118 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45 b3e118
        have b3e333 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e66 x x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e66
          | exact resolve b3e66 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e66
        have b3e383 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b3e333
        have b3e823 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e383
             have i₂ := b3e17 x x
             grind)
          | exact superpose b3e17 b3e383
          | (have j1 := b3e17 x x
             grind)
          | exact resolve b3e383 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e835 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
        clear b3e823
        have b3e847 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b3e835
             have r₂ := b3e120
             grind)
          | exact resolve b3e835 b3e120
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e120 b3e835
        have b3e920 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b3e847
        have b3e1071 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e383
             have i₂ := b3e920
             grind)
          | exact superpose b3e920 b3e383
          | exact resolve b3e383 b3e920
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e383 b3e920
        have b3e1078 : (σ x) = (σ y) := by grind
        clear b3e1071
        have b3e1138 : y = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 y
             have i₂ := b3e1078
             grind)
          | exact superpose b3e1078 b3e13
          | exact resolve b3e13 b3e1078
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1165 : x = y := by
          first
          | (have i₁ := b3e1138
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e1138
          | exact resolve b3e1138 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1138
        have b3e1182 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e1165
             grind)
          | exact superpose b3e1165 b3e19
          | exact resolve b3e19 b3e1165
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1183 : x = (M.op x x) := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e1165
             grind)
          | exact superpose b3e1165 b3e21
          | exact resolve b3e21 b3e1165
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1165
        have b3e1190 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e1182
             have i₂ := b3e1183
             grind)
          | exact superpose b3e1183 b3e1182
          | exact resolve b3e1182 b3e1183
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1182 b3e1183
        have b3e1191 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e1190
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e1190
          | exact resolve b3e1190 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1190
        have b3e1192 : False := by grind
        exact b3e1192
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op y x) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e19
            | exact resolve b4e19 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e28 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y x)) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e29 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) (σ x))) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 (σ y) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e33 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e29 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e29
            | exact resolve b4e29 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29
          have b4e34 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b4e28 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e28
            | exact resolve b4e28 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28
          have b4e58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X0 X1
               have i₂ := b4e18 (σ X0) (σ X1)
               grind)
            | exact superpose b4e18 b4e19
            | (have j1 := b4e18 (σ X0) (σ X1)
               grind)
            | exact resolve b4e19 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e90 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e33 (σ x)
               grind)
            | exact superpose b4e33 b4e20
            | exact resolve b4e20 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33
          have b4e100 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e90
               have i₂ := b4e34 x
               grind)
            | exact superpose b4e34 b4e90
            | exact resolve b4e90 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34 b4e90
          have b4e119 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k X0 (τ X1))
               have i₂ := b4e27 X1 X0
               grind)
            | exact superpose b4e27 b4e14
            | exact resolve b4e14 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e201 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
            intro X0
            grind
          clear b4e119
          have b4e215 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e201 X0
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e201
            | exact resolve b4e201 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e201
          have b4e255 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e100
               have i₂ := b4e58 x x
               grind)
            | exact superpose b4e58 b4e100
            | (have j1 := b4e58 x x
               grind)
            | (have r₁ := b4e100
               have r₂ := b4e58 x (M.op x x)
               grind)
            | exact resolve b4e100 b4e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e290 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e58 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e58
          have b4e291 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e290 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e290
          have b4e300 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b4e255
          have b4e1331 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e291 (τ X0)
               have i₂ := b4e27 X0 (τ X0)
               grind)
            | exact superpose b4e27 b4e291
            | (have j0 := b4e291 (τ X0)
               grind)
            | exact resolve b4e291 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27
          have b4e1335 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e1331 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e1331
            | (have j0 := b4e1331 X0
               grind)
            | exact resolve b4e1331 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1331
          have b4e1339 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e1335 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e1335
            | (have j0 := b4e1335 X0
               grind)
            | exact resolve b4e1335 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1335
          have b4e15748 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e300
               have i₂ := b4e18 x x
               grind)
            | exact superpose b4e18 b4e300
            | (have j1 := b4e18 (σ x) (σ x)
               grind)
            | exact resolve b4e300 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e300
          have b4e15750 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
          clear b4e15748
          have b4e15751 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
          clear b4e15750
          have b4e16127 : x = (k x (τ (σ x))) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e215 x
               have i₂ := b4e15751
               grind)
            | exact superpose b4e15751 b4e215
            | exact resolve b4e215 b4e15751
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e215 b4e15751
          have b4e16167 : x = (k x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e16127
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e16127
            | exact resolve b4e16127 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e16127
          have b4e16168 : x = (M.op x x) := by
            first
            | (have j1 := b4e1339 x
               grind)
            | (have r₁ := b4e16167
               have r₂ := b4e1339 x
               grind)
            | exact resolve b4e16167 b4e1339
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1339 b4e16167
          have b4e16541 : x = (k x x) := by grind
          have b4e16968 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e291 x
               have i₂ := b4e16541
               grind)
            | exact superpose b4e16541 b4e291
            | (have j0 := b4e291 x
               grind)
            | exact resolve b4e291 b4e16541
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e291 b4e16541
          have b4e16987 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b4e16968
          have b4e17676 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e100
               have i₂ := b4e16987
               grind)
            | exact superpose b4e16987 b4e100
            | exact resolve b4e100 b4e16987
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e100 b4e16987
          have b4e17722 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e17676
               have i₂ := b4e16168
               grind)
            | exact superpose b4e16168 b4e17676
            | exact resolve b4e17676 b4e16168
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e16168 b4e17676
          have b4e17723 : False := by grind
          exact b4e17723
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : y ≠ (M.op x x) := by grind
          have b5e22 : x = (M.op y x) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e26 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 (τ X0) X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e19
            | exact resolve b5e19 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X1 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e19
            | exact resolve b5e19 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e28 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y x)) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e30 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 X0 (M.op X0 x)
               have i₂ := b5e13 X0 X0 x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e32 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b5e28 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e28
            | exact resolve b5e28 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28
          have b5e33 : y = (k y (M.op y x)) := by grind
          have b5e35 : y = (k y x) := by
            first
            | (have i₁ := b5e33
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e33
            | exact resolve b5e33 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e36 : x ≠ x ∨ y = (M.op x x) ∨ (M.op y y) = (k x y) := by
            first
            | (have i₁ := b5e17 x y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e17
            | (have j0 := b5e17 x y
               grind)
            | (have r₁ := b5e17 x y
               have r₂ := b5e22
               grind)
            | exact resolve b5e17 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e39 : y = (M.op x x) ∨ (M.op y y) = (k x y) := by grind
          clear b5e36
          have b5e42 : (M.op y y) = (k x y) := by
            first
            | (have r₁ := b5e39
               have r₂ := b5e21
               grind)
            | exact resolve b5e39 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39
          have b5e44 : (M.op y x) = (k x y) := by
            first
            | (have i₁ := b5e42
               have i₂ := b5e32 y
               grind)
            | exact superpose b5e32 b5e42
            | exact resolve b5e42 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42
          have b5e45 : x = (k x y) := by
            first
            | (have i₁ := b5e44
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e44
            | exact resolve b5e44 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44
          have b5e49 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k X1 X2) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X2 ∨ (M.op X2 X1) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e18 X1 X2
               have i₂ := b5e18 X1 X0
               grind)
            | (have i₁ := b5e18 X0 X1
               have i₂ := b5e18 X0 (M.op X0 X0)
               grind)
            | exact superpose b5e18 b5e18
            | (have j0 := b5e18 X1 X2
               have j1 := b5e18 X1 X2
               grind)
            | exact resolve b5e18 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e50 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X0 X1
               have i₂ := b5e18 (σ X0) (σ X1)
               grind)
            | exact superpose b5e18 b5e19
            | (have j1 := b5e18 (σ X0) (σ X1)
               grind)
            | exact resolve b5e19 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e56 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e23
               have i₂ := b5e18 (σ x) X0
               grind)
            | (have i₁ := b5e23
               have i₂ := b5e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b5e18 b5e23
            | (have j1 := b5e18 (σ x) X0
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | exact resolve b5e23 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e86 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k (τ X0) X1)
               have i₂ := b5e26 X0 X1
               grind)
            | exact superpose b5e26 b5e14
            | exact resolve b5e14 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e94 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k X0 (τ X1))
               have i₂ := b5e27 X1 X0
               grind)
            | exact superpose b5e27 b5e14
            | exact resolve b5e14 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27
          have b5e97 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e86 X1 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e86
            | exact resolve b5e86 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e86
          have b5e151 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
            intro X0
            grind
          have b5e165 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e151 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e151
            | exact resolve b5e151 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e151
          have b5e169 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b5e56 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e56
          have b5e170 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e169
               have r₂ := b5e24
               grind)
            | exact resolve b5e169 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e169
          have b5e171 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e170
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e170
            | exact resolve b5e170 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e170
          have b5e172 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e171
               have i₂ := b5e45
               grind)
            | exact superpose b5e45 b5e171
            | exact resolve b5e171 b5e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45 b5e171
          have b5e173 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e172
               grind)
            | exact superpose b5e172 b5e20
            | exact resolve b5e20 b5e172
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e175 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b5e17 (σ y) (σ x)
               have i₂ := b5e172
               grind)
            | exact superpose b5e172 b5e17
            | (have j0 := b5e17 (σ y) (σ x)
               grind)
            | exact resolve b5e17 b5e172
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e177 : (M.op (σ x) (σ x)) = (σ (k y x)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e175
               have i₂ := b5e19 y x
               grind)
            | exact superpose b5e19 b5e175
            | exact resolve b5e175 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e175
          have b5e178 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e173
               have i₂ := b5e32 x
               grind)
            | exact superpose b5e32 b5e173
            | exact resolve b5e173 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e173
          have b5e179 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e177
               have i₂ := b5e35
               grind)
            | exact superpose b5e35 b5e177
            | exact resolve b5e177 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e177
          have b5e180 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
            first
            | (have r₁ := b5e179
               have r₂ := b5e23
               grind)
            | exact resolve b5e179 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e179
          have b5e231 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e30 (σ X0) X1
               have i₂ := b5e50 X0 X0
               grind)
            | exact superpose b5e50 b5e30
            | (have j1 := b5e50 X0 X0
               grind)
            | exact resolve b5e30 b5e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30
          have b5e258 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e17 (σ X0) (σ X1)
               have i₂ := b5e50 X0 X1
               grind)
            | exact superpose b5e50 b5e17
            | (have j0 := b5e17 (σ X0) (σ X1)
               have j1 := b5e50 X0 X1
               grind)
            | (have r₁ := b5e17 (σ X1) (σ X1)
               have r₂ := b5e50 X1 X1
               grind)
            | (have r₁ := b5e17 (σ X0) (σ X1)
               have r₂ := b5e50 X0 X1
               grind)
            | exact resolve b5e17 b5e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50
          have b5e264 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e258 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e258
          have b5e265 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e264 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e264
          have b5e270 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e231 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e231
          have b5e277 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e265 X0 X1
               have i₂ := b5e19 X0 X1
               grind)
            | exact superpose b5e19 b5e265
            | (have j0 := b5e265 X0 X1
               grind)
            | exact resolve b5e265 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e265
          have b5e357 : ∀ X0 : G, y = (M.op y x) ∨ (k y X0) = (M.op y X0) ∨ x = X0 ∨ y = (M.op X0 y) ∨ y = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b5e35
               have i₂ := b5e49 x y X0
               grind)
            | exact superpose b5e49 b5e35
            | (have j1 := b5e49 X0 y X0
               grind)
            | exact resolve b5e35 b5e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35 b5e49
          have b5e362 : ∀ X0 : G, x = y ∨ (k y X0) = (M.op y X0) ∨ x = X0 ∨ y = (M.op X0 y) ∨ y = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b5e357 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e357
            | (have j0 := b5e357 X0
               grind)
            | exact resolve b5e357 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e357
          have b5e370 : ∀ X0 : G, y = (M.op X0 x) ∨ x = y ∨ (k y X0) = (M.op y X0) ∨ x = X0 ∨ y = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b5e362 X0
               have i₂ := b5e32 X0
               grind)
            | exact superpose b5e32 b5e362
            | (have j0 := b5e362 X0
               grind)
            | exact resolve b5e362 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e362
          have b5e378 : ∀ X0 : G, y = (M.op x x) ∨ y = (M.op X0 x) ∨ x = y ∨ (k y X0) = (M.op y X0) ∨ x = X0 := by
            intro X0
            first
            | (have i₁ := b5e370 X0
               have i₂ := b5e32 x
               grind)
            | exact superpose b5e32 b5e370
            | (have j0 := b5e370 X0
               grind)
            | exact resolve b5e370 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e370
          have b5e384 : ∀ X0 : G, (k y X0) = (M.op y X0) ∨ x = y ∨ y = (M.op X0 x) ∨ x = X0 := by
            intro X0
            first
            | (have j0 := b5e378 X0
               grind)
            | (have r₁ := b5e378 X0
               have r₂ := b5e21
               grind)
            | (have r₁ := b5e378 x
               have r₂ := b5e21
               grind)
            | exact resolve b5e378 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e378
          have b5e404 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op (σ (σ X0)) (σ (σ X0)))))) := by
            intro X0
            first
            | (have i₁ := b5e94 X0 (τ (M.op (σ (σ X0)) (σ (σ X0))))
               have i₂ := b5e165 (σ X0)
               grind)
            | exact superpose b5e165 b5e94
            | exact resolve b5e94 b5e165
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e94
          have b5e410 : ∀ X0 : G, (k X0 (τ (τ (M.op (σ (σ X0)) (σ (σ X0)))))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e404 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e404
            | exact resolve b5e404 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e404
          have b5e1840 : ∀ X0 X1 : G, (M.op X1 (σ (σ X0))) = (M.op X1 (σ (σ (k X0 X0)))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e270 (σ X0) X1
               have i₂ := b5e19 X0 X0
               grind)
            | exact superpose b5e19 b5e270
            | (have j0 := b5e270 (σ X0) X1
               grind)
            | exact resolve b5e270 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e270
          have b5e6197 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e277 (τ X1) (τ X0)
               have i₂ := b5e97 X0 X1
               grind)
            | exact superpose b5e97 b5e277
            | (have j0 := b5e277 (τ X1) (τ (k X0 X1))
               grind)
            | exact resolve b5e277 b5e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e277
          have b5e6660 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e6197 X0 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e6197
            | (have j0 := b5e6197 X0 X1
               grind)
            | exact resolve b5e6197 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6197
          have b5e6708 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e6660 X0 X1
               have i₂ := b5e15 (k X0 X1)
               grind)
            | exact superpose b5e15 b5e6660
            | (have j0 := b5e6660 X0 X1
               grind)
            | exact resolve b5e6660 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6660
          have b5e6714 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (k X0 X1) = (M.op X1 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e6708 X0 X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e6708
            | (have j0 := b5e6708 X0 X1
               grind)
            | exact resolve b5e6708 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6708
          have b5e6717 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e6714 X0 X1
               have i₂ := b5e15 X1
               grind)
            | exact superpose b5e15 b5e6714
            | (have j0 := b5e6714 X0 X1
               grind)
            | exact resolve b5e6714 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6714
          have b5e6718 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e6717 X0 X1
               have i₂ := b5e15 X1
               grind)
            | exact superpose b5e15 b5e6717
            | (have j0 := b5e6717 X0 X1
               grind)
            | exact resolve b5e6717 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6717
          have b5e6719 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e6718 X0 X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e6718
            | (have j0 := b5e6718 X0 X1
               grind)
            | exact resolve b5e6718 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6718
          have b5e6720 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e6719 X0 X1
               have i₂ := b5e15 (k X0 X1)
               grind)
            | exact superpose b5e15 b5e6719
            | (have j0 := b5e6719 X0 X1
               grind)
            | exact resolve b5e6719 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6719
          have b5e57513 : ∀ X0 X1 : G, (k X0 (τ (τ (σ (σ X0))))) = X0 ∨ (M.op X1 (σ (σ X0))) = (M.op X1 (σ (σ (k X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e410 X0
               have i₂ := b5e1840 X0 X1
               grind)
            | exact superpose b5e1840 b5e410
            | (have j1 := b5e1840 X0 X1
               grind)
            | exact resolve b5e410 b5e1840
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e410 b5e1840
          have b5e57523 : ∀ X0 X1 : G, (k X0 (τ (σ X0))) = X0 ∨ (M.op X1 (σ (σ X0))) = (M.op X1 (σ (σ (k X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e57513 X0 X1
               have i₂ := b5e14 (σ X0)
               grind)
            | exact superpose b5e14 b5e57513
            | (have j0 := b5e57513 X0 X1
               grind)
            | exact resolve b5e57513 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e57513
          have b5e57531 : ∀ X0 X1 : G, (M.op X1 (σ (σ X0))) = (M.op X1 (σ (σ (k X0 X0)))) ∨ (k X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e57523 X0 X1
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e57523
            | (have j0 := b5e57523 X0 X1
               grind)
            | exact resolve b5e57523 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e57523
          have b5e57734 : ∀ X0 X1 : G, (M.op X1 (σ (σ (τ X0)))) = (M.op X1 (σ (k X0 (σ (τ X0))))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e57531 (τ X0) X1
               have i₂ := b5e26 X0 (τ X0)
               grind)
            | exact superpose b5e26 b5e57531
            | (have j0 := b5e57531 (τ X0) X1
               grind)
            | exact resolve b5e57531 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e57531
          have b5e57766 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (k X0 X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e57734 X0 X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e57734
            | (have j0 := b5e57734 X0 X1
               grind)
            | exact resolve b5e57734 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e57734
          have b5e57777 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (k X0 X0))) ∨ (τ X0) = (τ (k X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e57766 X0 X1
               have i₂ := b5e97 X0 X0
               grind)
            | exact superpose b5e97 b5e57766
            | (have j0 := b5e57766 X0 X1
               grind)
            | exact resolve b5e57766 b5e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e97 b5e57766
          have b5e58104 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op y y))) ∨ (τ y) = (τ (M.op y y)) ∨ x = y ∨ y = (M.op y x) ∨ x = y := by
            intro X0
            first
            | (have i₁ := b5e57777 y x
               have i₂ := b5e384 y
               grind)
            | exact superpose b5e384 b5e57777
            | (have j1 := b5e384 y
               grind)
            | exact resolve b5e57777 b5e384
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e384 b5e57777
          have b5e58135 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op y y))) ∨ (τ y) = (τ (M.op y y)) ∨ x = y ∨ y = (M.op y x) := by
            intro X0
            first
            | (have j0 := b5e58104 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58104
          have b5e58141 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op y x))) ∨ (τ y) = (τ (M.op y y)) ∨ x = y ∨ y = (M.op y x) := by
            intro X0
            first
            | (have i₁ := b5e58135 X0
               have i₂ := b5e32 y
               grind)
            | exact superpose b5e32 b5e58135
            | exact resolve b5e58135 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58135
          have b5e58149 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (τ y) = (τ (M.op y y)) ∨ x = y ∨ y = (M.op y x) := by
            intro X0
            first
            | (have i₁ := b5e58141 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e58141
            | exact resolve b5e58141 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58141
          have b5e58153 : ∀ X0 : G, (τ y) = (τ (M.op y x)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ x = y ∨ y = (M.op y x) := by
            intro X0
            first
            | (have i₁ := b5e58149 X0
               have i₂ := b5e32 y
               grind)
            | exact superpose b5e32 b5e58149
            | (have j0 := b5e58149 X0
               grind)
            | exact resolve b5e58149 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32 b5e58149
          have b5e58155 : ∀ X0 : G, (τ y) = (τ x) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ x = y ∨ y = (M.op y x) := by
            intro X0
            first
            | (have i₁ := b5e58153 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e58153
            | (have j0 := b5e58153 X0
               grind)
            | exact resolve b5e58153 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58153
          have b5e58158 : ∀ X0 : G, x = y ∨ (τ y) = (τ x) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ x = y := by
            intro X0
            first
            | (have i₁ := b5e58155 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e58155
            | (have j0 := b5e58155 X0
               grind)
            | exact resolve b5e58155 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58155
          have b5e58159 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (τ y) = (τ x) ∨ x = y := by
            intro X0
            first
            | (have j0 := b5e58158 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58158
          have b5e58193 : (σ x) = (M.op (σ x) (σ x)) ∨ (τ y) = (τ x) ∨ x = y := by
            first
            | (have i₁ := b5e172
               have i₂ := b5e58159 (σ x)
               grind)
            | exact superpose b5e58159 b5e172
            | exact resolve b5e172 b5e58159
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e172 b5e58159
          have b5e58279 : x = (k x (τ (σ x))) ∨ (τ y) = (τ x) ∨ x = y := by
            first
            | (have i₁ := b5e165 x
               have i₂ := b5e58193
               grind)
            | exact superpose b5e58193 b5e165
            | exact resolve b5e165 b5e58193
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e165 b5e58193
          have b5e58315 : x = (k x x) ∨ (τ y) = (τ x) ∨ x = y := by
            first
            | (have i₁ := b5e58279
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e58279
            | exact resolve b5e58279 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58279
          have b5e58443 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (τ y) = (τ x) ∨ x = y := by
            first
            | (have i₁ := b5e6720 x x
               have i₂ := b5e58315
               grind)
            | exact superpose b5e58315 b5e6720
            | (have j0 := b5e6720 x x
               grind)
            | exact resolve b5e6720 b5e58315
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6720 b5e58315
          have b5e58446 : x = (M.op x x) ∨ (τ y) = (τ x) ∨ x = y := by grind
          clear b5e58443
          have b5e58475 : (σ x) ≠ (σ x) ∨ (τ y) = (τ x) ∨ x = y := by
            first
            | (have i₁ := b5e178
               have i₂ := b5e58446
               grind)
            | exact superpose b5e58446 b5e178
            | exact resolve b5e178 b5e58446
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e178 b5e58446
          have b5e58531 : (τ y) = (τ x) ∨ x = y := by grind
          clear b5e58475
          have b5e58541 : y = (σ (τ x)) ∨ x = y := by
            first
            | (have i₁ := b5e15 y
               have i₂ := b5e58531
               grind)
            | exact superpose b5e58531 b5e15
            | exact resolve b5e15 b5e58531
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58531
          have b5e58634 : x = y ∨ x = y := by
            first
            | (have i₁ := b5e58541
               have i₂ := b5e15 x
               grind)
            | exact superpose b5e15 b5e58541
            | exact resolve b5e58541 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58541
          have b5e58635 : x = y := by grind
          clear b5e58634
          have b5e58692 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e58635
               grind)
            | exact superpose b5e58635 b5e24
            | exact resolve b5e24 b5e58635
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e58698 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e180
               have i₂ := b5e58635
               grind)
            | exact superpose b5e58635 b5e180
            | exact resolve b5e180 b5e58635
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e180 b5e58635
          have b5e58718 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b5e58698
          have b5e58721 : False := by grind
          exact b5e58721
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : x ≠ (M.op y x) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e24 : (σ x) = (k (σ x) (σ y)) := by grind
        have b6e25 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b6e24
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e24
          | exact resolve b6e24 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24
        have b6e42 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X1 X0 (M.op X0 x)
             have i₂ := b6e12 X0 X0 x
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e44 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e42 (σ x) X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e42
          | exact resolve b6e42 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42
        have b6e57 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e44 (σ x)
             grind)
          | exact superpose b6e44 b6e19
          | exact resolve b6e19 b6e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e44
        have b6e64 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e57
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e57
          | exact resolve b6e57 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e57
        have b6e72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X0 X1
             have i₂ := b6e17 (σ X0) (σ X1)
             grind)
          | exact superpose b6e17 b6e18
          | (have j1 := b6e17 (σ X0) (σ X1)
             grind)
          | exact resolve b6e18 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e75 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
          first
          | (have i₁ := b6e25
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e25
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e25 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e87 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
          first
          | (have r₁ := b6e75
             have r₂ := b6e20
             grind)
          | exact resolve b6e75 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e75
        have b6e93 : (σ (M.op x y)) = (σ x) := by
          first
          | (have r₁ := b6e87
             have r₂ := b6e21
             grind)
          | exact resolve b6e87 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e87
        have b6e146 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b6e64
             have i₂ := b6e93
             grind)
          | exact superpose b6e93 b6e64
          | exact resolve b6e64 b6e93
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64 b6e93
        have b6e312 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e72 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e72
          | exact resolve b6e72 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e72
        have b6e362 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) := by grind
        clear b6e312
        have b6e380 : (σ y) = (σ (k x x)) := by
          first
          | (have r₁ := b6e362
             have r₂ := b6e146
             grind)
          | exact resolve b6e362 b6e146
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e362
        have b6e417 : (k x x) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e380
             grind)
          | exact superpose b6e380 b6e13
          | exact resolve b6e13 b6e380
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e437 : y = (k x x) := by
          first
          | (have i₁ := b6e417
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e417
          | exact resolve b6e417 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e417
        have b6e497 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e437
             grind)
          | exact superpose b6e437 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e437
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e437
        have b6e498 : y = (M.op x x) ∨ x = (M.op x x) := by grind
        clear b6e497
        have b6e500 : x = (M.op x x) := by
          first
          | (have r₁ := b6e498
             have r₂ := b6e20
             grind)
          | exact resolve b6e498 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e498
        have b6e547 : x = (k x x) := by grind
        clear b6e500
        have b6e736 : (σ x) = (σ y) := by
          first
          | (have i₁ := b6e380
             have i₂ := b6e547
             grind)
          | exact superpose b6e547 b6e380
          | exact resolve b6e380 b6e547
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e380 b6e547
        have b6e747 : False := by grind
        exact b6e747
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : x ≠ (M.op y x) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e28 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) (σ x))) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ y) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e30 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X1 X0 (M.op X0 x)
               have i₂ := b7e13 X0 X0 x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e32 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e28 X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e28
            | exact resolve b7e28 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28
          have b7e36 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op X0 X0) X0)) := by
            intro X0
            grind
          clear b7e30
          have b7e40 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e17 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e17
            | (have j0 := b7e17 (σ x) (σ y)
               grind)
            | (have r₁ := b7e17 (σ x) (σ y)
               have r₂ := b7e24
               grind)
            | exact resolve b7e17 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e43 : (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear b7e40
          have b7e46 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
            first
            | (have r₁ := b7e43
               have r₂ := b7e23
               grind)
            | exact resolve b7e43 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e43
          have b7e47 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e46
               have i₂ := b7e32 (σ y)
               grind)
            | exact superpose b7e32 b7e46
            | exact resolve b7e46 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e48 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e47
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e47
            | exact resolve b7e47 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
          have b7e49 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e48
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e48
            | exact resolve b7e48 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e52 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e49
               grind)
            | exact superpose b7e49 b7e14
            | exact resolve b7e14 b7e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e53 : x = (k x y) := by
            first
            | (have i₁ := b7e52
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e52
            | exact resolve b7e52 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
          have b7e60 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e19 X0 X1
               have i₂ := b7e18 (σ X0) (σ X1)
               grind)
            | exact superpose b7e18 b7e19
            | (have j1 := b7e18 (σ X0) (σ X1)
               grind)
            | exact resolve b7e19 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e61 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b7e49
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e49
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e49 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e71 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
            first
            | (have r₁ := b7e61
               have r₂ := b7e21
               grind)
            | exact resolve b7e61 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e74 : (σ (M.op x y)) = (σ x) := by
            first
            | (have r₁ := b7e71
               have r₂ := b7e22
               grind)
            | exact resolve b7e71 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e76 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e53
               grind)
            | exact superpose b7e53 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53
          have b7e77 : x = (M.op x y) ∨ x = (M.op y x) := by
            first
            | (have r₁ := b7e76
               have r₂ := b7e21
               grind)
            | exact resolve b7e76 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e76
          have b7e79 : x = (M.op x y) := by
            first
            | (have r₁ := b7e77
               have r₂ := b7e22
               grind)
            | exact resolve b7e77 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77
          have b7e82 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e32 (σ x)
               grind)
            | exact superpose b7e32 b7e20
            | exact resolve b7e20 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e92 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e82
               have i₂ := b7e74
               grind)
            | exact superpose b7e74 b7e82
            | exact resolve b7e82 b7e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e74 b7e82
          have b7e290 : ∀ X0 : G, (σ y) = (M.op (σ X0) (σ x)) ∨ (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e32 (σ X0)
               have i₂ := b7e60 y X0
               grind)
            | exact superpose b7e60 b7e32
            | (have j1 := b7e60 y X0
               grind)
            | exact resolve b7e32 b7e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e296 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e60 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60
          have b7e297 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e296 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e296
          have b7e314 : ∀ X0 : G, (σ X0) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ X0) (σ x)) ∨ (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e290 X0
               have i₂ := b7e32 (σ y)
               grind)
            | exact superpose b7e32 b7e290
            | (have j0 := b7e290 X0
               grind)
            | exact resolve b7e290 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e290
          have b7e353 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (σ x) := by
            intro X0
            first
            | (have i₁ := b7e314 X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e314
            | (have j0 := b7e314 X0
               grind)
            | exact resolve b7e314 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e314
          have b7e2536 : (M.op (σ y) (σ x)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e32 (σ y)
               have i₂ := b7e353 y
               grind)
            | exact superpose b7e353 b7e32
            | (have j1 := b7e353 y
               grind)
            | exact resolve b7e32 b7e353
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32 b7e353
          have b7e2600 : (σ x) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e2536
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e2536
            | exact resolve b7e2536 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2536
          have b7e2641 : (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e2600
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e2600
            | exact resolve b7e2600 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2600
          have b7e2642 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
          clear b7e2641
          have b7e2676 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e2642
               grind)
            | exact superpose b7e2642 b7e14
            | exact resolve b7e14 b7e2642
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e2716 : x = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e2676
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e2676
            | exact resolve b7e2676 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2676
          have b7e2865 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e18 y y
               have i₂ := b7e2716
               grind)
            | exact superpose b7e2716 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e2716
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2716
          have b7e2866 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b7e2865
          have b7e7584 : y = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b7e2866
          have b7e8241 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e2642
               have i₂ := b7e7584
               grind)
            | exact superpose b7e7584 b7e2642
            | exact resolve b7e2642 b7e7584
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2642 b7e7584
          have b7e8262 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b7e8241
          have b7e8668 : x = (k x (M.op x y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e36 y
               have i₂ := b7e8262
               grind)
            | exact superpose b7e8262 b7e36
            | exact resolve b7e36 b7e8262
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36 b7e8262
          have b7e8701 : x = (k x x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e8668
               have i₂ := b7e79
               grind)
            | exact superpose b7e79 b7e8668
            | exact resolve b7e8668 b7e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e79 b7e8668
          have b7e9293 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e297 x
               have i₂ := b7e8701
               grind)
            | exact superpose b7e8701 b7e297
            | (have j0 := b7e297 x
               grind)
            | exact resolve b7e297 b7e8701
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e297 b7e8701
          have b7e9312 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
          clear b7e9293
          have b7e9318 : (σ x) = (σ y) := by
            first
            | (have r₁ := b7e9312
               have r₂ := b7e92
               grind)
            | exact resolve b7e9312 b7e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e9312
          have b7e9489 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e9318
               grind)
            | exact superpose b7e9318 b7e24
            | exact resolve b7e24 b7e9318
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e9318
          have b7e9586 : False := by grind
          exact b7e9586
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x x) := by grind
          have b8e22 : x ≠ (M.op y x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e60 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 (σ x) X0
               grind)
            | (have i₁ := b8e23
               have i₂ := b8e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b8e18 b8e23
            | (have j1 := b8e18 (σ x) X0
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e117 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b8e60 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60
          have b8e118 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e117
               have r₂ := b8e24
               grind)
            | exact resolve b8e117 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e117
          have b8e119 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e118
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e118
            | exact resolve b8e118 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e118
          have b8e156 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e119
               grind)
            | exact superpose b8e119 b8e20
            | exact resolve b8e20 b8e119
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e119
          have b8e271 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e156
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e156
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e156 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e156
          have b8e272 : y = (M.op x x) ∨ x = (M.op y x) := by grind
          clear b8e271
          have b8e274 : x = (M.op y x) := by
            first
            | (have r₁ := b8e272
               have r₂ := b8e21
               grind)
            | exact resolve b8e272 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e272
          have b8e276 : False := by grind
          exact b8e276

/-- `Equation3320`: `x ◇ y = x ◇ (y ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_x_x_x_pxy_Equation3320 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3320 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3320.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e36 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1 X0 (M.op X0 x)
           have i₂ := b0e11 X0 X0 x
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e47 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e36 x X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e36
        | exact resolve b0e36 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e48 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e36 (σ x) X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e36
        | exact resolve b0e36 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36
      have b0e153 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e48 (σ x)
           grind)
        | exact superpose b0e48 b0e18
        | exact resolve b0e18 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48
      have b0e154 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e153
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e153
        | exact resolve b0e153 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e153
      have b0e159 : (σ y) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e154
           have i₂ := b0e47 x
           grind)
        | exact superpose b0e47 b0e154
        | exact resolve b0e154 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47 b0e154
      have b0e160 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e159
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e159
        | exact resolve b0e159 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e159
      have b0e161 : False := by grind
      exact b0e161
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X1 (τ X0)
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e18
          | exact resolve b1e18 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X0 X1
             have i₂ := b1e17 (σ X0) (σ X1)
             grind)
          | exact superpose b1e17 b1e18
          | (have j1 := b1e17 (σ X0) (σ X1)
             grind)
          | exact resolve b1e18 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e145 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e13 (k X0 (τ X1))
             have i₂ := b1e26 X1 X0
             grind)
          | exact superpose b1e26 b1e13
          | exact resolve b1e13 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e259 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b1e145
        have b1e273 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e259 X0
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e259
          | exact resolve b1e259 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e259
        have b1e319 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e65 x x
             grind)
          | exact superpose b1e65 b1e21
          | (have j1 := b1e65 x x
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e65 x y
             grind)
          | exact resolve b1e21 b1e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e65
        have b1e361 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b1e319
        have b1e1781 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e361
             have i₂ := b1e17 x x
             grind)
          | exact superpose b1e17 b1e361
          | (have j1 := b1e17 (σ x) (σ x)
             grind)
          | exact resolve b1e361 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e361
        have b1e1782 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b1e1781
        have b1e1783 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e1782
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1782
          | exact resolve b1e1782 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1782
        have b1e1784 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b1e1783
        have b1e1790 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b1e1784
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1784
          | exact resolve b1e1784 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1784
        have b1e1800 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b1e273 x
             have i₂ := b1e1790
             grind)
          | exact superpose b1e1790 b1e273
          | exact resolve b1e273 b1e1790
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e273 b1e1790
        have b1e1815 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b1e1800
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e1800
          | exact resolve b1e1800 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1800
        have b1e1933 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b1e17 x x
             have i₂ := b1e1815
             grind)
          | exact superpose b1e1815 b1e17
          | (have j0 := b1e17 x x
             grind)
          | exact resolve b1e17 b1e1815
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1815
        have b1e1934 : x = (M.op x x) ∨ x = y := by grind
        clear b1e1933
        have b1e1943 : x = y ∨ x = y := by
          first
          | (have i₁ := b1e1934
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1934
          | exact resolve b1e1934 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1934
        have b1e1944 : x = y := by grind
        clear b1e1943
        have b1e1972 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e1944
             grind)
          | exact superpose b1e1944 b1e22
          | exact resolve b1e22 b1e1944
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2675 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e1972
             grind)
          | exact superpose b1e1972 b1e21
          | exact resolve b1e21 b1e1972
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1972
        have b1e2694 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e2675
             have i₂ := b1e1944
             grind)
          | exact superpose b1e1944 b1e2675
          | exact resolve b1e2675 b1e1944
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1944 b1e2675
        have b1e2695 : False := by grind
        exact b1e2695
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : x = (k x y) := by grind
        have b2e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e18
          | exact resolve b2e18 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e29 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 X0 (M.op X0 x)
             have i₂ := b2e12 X0 X0 x
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e39 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b2e29 x X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e29
          | exact resolve b2e29 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29
        have b2e59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e17 (σ X0) (σ X1)
             grind)
          | exact superpose b2e17 b2e18
          | (have j1 := b2e17 (σ X0) (σ X1)
             grind)
          | exact resolve b2e18 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e67 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e17 (σ x) X0
             grind)
          | (have i₁ := b2e21
             have i₂ := b2e17 X0 (M.op (σ x) (σ x))
             grind)
          | exact superpose b2e17 b2e21
          | (have j1 := b2e17 (σ x) X0
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | exact resolve b2e21 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e108 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k X0 (τ X1))
             have i₂ := b2e26 X1 X0
             grind)
          | exact superpose b2e26 b2e13
          | exact resolve b2e13 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26
        have b2e179 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e67 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e67
        have b2e180 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e179
             have r₂ := b2e22
             grind)
          | exact resolve b2e179 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e179
        have b2e181 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e180
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e180
          | exact resolve b2e180 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e180
        have b2e182 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e181
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e181
          | exact resolve b2e181 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e181
        have b2e183 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e182
             grind)
          | exact superpose b2e182 b2e19
          | exact resolve b2e19 b2e182
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e182
        have b2e188 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e183
             have i₂ := b2e39 x
             grind)
          | exact superpose b2e39 b2e183
          | exact resolve b2e183 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39 b2e183
        have b2e189 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e188
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e188
          | exact resolve b2e188 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e188
        have b2e247 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e59 x x
             grind)
          | exact superpose b2e59 b2e21
          | (have j1 := b2e59 x x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e59 x y
             grind)
          | exact resolve b2e21 b2e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e59
        have b2e287 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e247
        have b2e328 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b2e108
        have b2e342 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e328 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e328
          | exact resolve b2e328 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e328
        have b2e1544 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e287
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e287
          | (have j1 := b2e17 (σ x) (σ x)
             grind)
          | exact resolve b2e287 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e287
        have b2e1545 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e1544
        have b2e1546 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e1545
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1545
          | exact resolve b2e1545 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1545
        have b2e1547 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e1546
        have b2e1553 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e1547
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1547
          | exact resolve b2e1547 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1547
        have b2e1563 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b2e342 x
             have i₂ := b2e1553
             grind)
          | exact superpose b2e1553 b2e342
          | exact resolve b2e342 b2e1553
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e342 b2e1553
        have b2e1578 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e1563
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e1563
          | exact resolve b2e1563 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1563
        have b2e1607 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b2e17 x x
             have i₂ := b2e1578
             grind)
          | exact superpose b2e1578 b2e17
          | (have j0 := b2e17 x x
             grind)
          | exact resolve b2e17 b2e1578
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1578
        have b2e1608 : x = (M.op x x) ∨ x = y := by grind
        clear b2e1607
        have b2e1617 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e1608
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1608
          | exact resolve b2e1608 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1608
        have b2e1618 : x = y := by grind
        clear b2e1617
        have b2e1718 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e189
             have i₂ := b2e1618
             grind)
          | exact superpose b2e1618 b2e189
          | exact resolve b2e189 b2e1618
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e189 b2e1618
        have b2e1720 : False := by grind
        exact b2e1720
  · rcases eq_or_ne (M.op y x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e21 : x = (M.op y x) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e40 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y x)) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 y x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e43 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X1 X0 (M.op X0 x)
             have i₂ := b3e12 X0 X0 x
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e45 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b3e40 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e40
          | exact resolve b3e40 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40
        have b3e63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e18 X0 X1
             have i₂ := b3e17 (σ X0) (σ X1)
             grind)
          | exact superpose b3e17 b3e18
          | (have j1 := b3e17 (σ X0) (σ X1)
             grind)
          | exact resolve b3e18 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e79 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e43 (σ x) X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e43
          | exact resolve b3e43 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43
        have b3e106 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e79 (σ x)
             grind)
          | exact superpose b3e79 b3e19
          | exact resolve b3e19 b3e79
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e79
        have b3e115 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b3e106
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e106
          | exact resolve b3e106 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e106
        have b3e117 : (σ y) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e115
             have i₂ := b3e45 x
             grind)
          | exact superpose b3e45 b3e115
          | exact resolve b3e115 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45 b3e115
        have b3e330 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e63 x x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e63
          | exact resolve b3e63 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e63
        have b3e380 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b3e330
        have b3e818 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e380
             have i₂ := b3e17 x x
             grind)
          | exact superpose b3e17 b3e380
          | (have j1 := b3e17 x x
             grind)
          | exact resolve b3e380 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e830 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
        clear b3e818
        have b3e842 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b3e830
             have r₂ := b3e117
             grind)
          | exact resolve b3e830 b3e117
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e117 b3e830
        have b3e863 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b3e842
        have b3e1025 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e380
             have i₂ := b3e863
             grind)
          | exact superpose b3e863 b3e380
          | exact resolve b3e380 b3e863
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e380 b3e863
        have b3e1032 : (σ x) = (σ y) := by grind
        clear b3e1025
        have b3e1086 : y = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 y
             have i₂ := b3e1032
             grind)
          | exact superpose b3e1032 b3e13
          | exact resolve b3e13 b3e1032
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1109 : x = y := by
          first
          | (have i₁ := b3e1086
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e1086
          | exact resolve b3e1086 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1086
        have b3e1178 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e1109
             grind)
          | exact superpose b3e1109 b3e19
          | exact resolve b3e19 b3e1109
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1179 : x = (M.op x x) := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e1109
             grind)
          | exact superpose b3e1109 b3e21
          | exact resolve b3e21 b3e1109
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1109
        have b3e1186 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e1178
             have i₂ := b3e1179
             grind)
          | exact superpose b3e1179 b3e1178
          | exact resolve b3e1178 b3e1179
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1178 b3e1179
        have b3e1187 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e1186
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e1186
          | exact resolve b3e1186 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1186
        have b3e1188 : False := by grind
        exact b3e1188
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op y x) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e19
            | exact resolve b4e19 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e28 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y x)) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e29 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) (σ x))) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 (σ y) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e33 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e29 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e29
            | exact resolve b4e29 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29
          have b4e34 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b4e28 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e28
            | exact resolve b4e28 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28
          have b4e54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X0 X1
               have i₂ := b4e18 (σ X0) (σ X1)
               grind)
            | exact superpose b4e18 b4e19
            | (have j1 := b4e18 (σ X0) (σ X1)
               grind)
            | exact resolve b4e19 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e86 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e33 (σ x)
               grind)
            | exact superpose b4e33 b4e20
            | exact resolve b4e20 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33
          have b4e96 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e86
               have i₂ := b4e34 x
               grind)
            | exact superpose b4e34 b4e86
            | exact resolve b4e86 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34 b4e86
          have b4e115 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k X0 (τ X1))
               have i₂ := b4e27 X1 X0
               grind)
            | exact superpose b4e27 b4e14
            | exact resolve b4e14 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e197 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
            intro X0
            grind
          clear b4e115
          have b4e211 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e197 X0
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e197
            | exact resolve b4e197 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e197
          have b4e251 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e96
               have i₂ := b4e54 x x
               grind)
            | exact superpose b4e54 b4e96
            | (have j1 := b4e54 x x
               grind)
            | (have r₁ := b4e96
               have r₂ := b4e54 x (M.op x x)
               grind)
            | exact resolve b4e96 b4e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e286 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e54 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54
          have b4e287 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e286 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e286
          have b4e296 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b4e251
          have b4e1326 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e287 (τ X0)
               have i₂ := b4e27 X0 (τ X0)
               grind)
            | exact superpose b4e27 b4e287
            | (have j0 := b4e287 (τ X0)
               grind)
            | exact resolve b4e287 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27
          have b4e1330 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e1326 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e1326
            | (have j0 := b4e1326 X0
               grind)
            | exact resolve b4e1326 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1326
          have b4e1334 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e1330 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e1330
            | (have j0 := b4e1330 X0
               grind)
            | exact resolve b4e1330 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1330
          have b4e15175 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e296
               have i₂ := b4e18 x x
               grind)
            | exact superpose b4e18 b4e296
            | (have j1 := b4e18 (σ x) (σ x)
               grind)
            | exact resolve b4e296 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e296
          have b4e15177 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
          clear b4e15175
          have b4e15178 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
          clear b4e15177
          have b4e15550 : x = (k x (τ (σ x))) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e211 x
               have i₂ := b4e15178
               grind)
            | exact superpose b4e15178 b4e211
            | exact resolve b4e211 b4e15178
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e211 b4e15178
          have b4e15590 : x = (k x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e15550
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e15550
            | exact resolve b4e15550 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e15550
          have b4e15591 : x = (M.op x x) := by
            first
            | (have j1 := b4e1334 x
               grind)
            | (have r₁ := b4e15590
               have r₂ := b4e1334 x
               grind)
            | exact resolve b4e15590 b4e1334
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1334 b4e15590
          have b4e15960 : x = (k x x) := by grind
          have b4e16596 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e287 x
               have i₂ := b4e15960
               grind)
            | exact superpose b4e15960 b4e287
            | (have j0 := b4e287 x
               grind)
            | exact resolve b4e287 b4e15960
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e287 b4e15960
          have b4e16615 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b4e16596
          have b4e17154 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e96
               have i₂ := b4e16615
               grind)
            | exact superpose b4e16615 b4e96
            | exact resolve b4e96 b4e16615
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e96 b4e16615
          have b4e17201 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e17154
               have i₂ := b4e15591
               grind)
            | exact superpose b4e15591 b4e17154
            | exact resolve b4e17154 b4e15591
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e15591 b4e17154
          have b4e17202 : False := by grind
          exact b4e17202
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : y ≠ (M.op x x) := by grind
          have b5e22 : x = (M.op y x) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e26 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 (τ X0) X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e19
            | exact resolve b5e19 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X1 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e19
            | exact resolve b5e19 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e28 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y x)) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e30 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 X0 (M.op X0 x)
               have i₂ := b5e13 X0 X0 x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e32 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b5e28 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e28
            | exact resolve b5e28 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28
          have b5e36 : x ≠ x ∨ y = (M.op x x) ∨ x = (k x y) := by
            first
            | (have i₁ := b5e17 x y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e17
            | (have j0 := b5e17 x y
               grind)
            | (have r₁ := b5e17 x y
               have r₂ := b5e22
               grind)
            | exact resolve b5e17 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e39 : y = (M.op x x) ∨ x = (k x y) := by grind
          clear b5e36
          have b5e42 : x = (k x y) := by
            first
            | (have r₁ := b5e39
               have r₂ := b5e21
               grind)
            | exact resolve b5e39 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39
          have b5e48 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X0 X1
               have i₂ := b5e18 (σ X0) (σ X1)
               grind)
            | exact superpose b5e18 b5e19
            | (have j1 := b5e18 (σ X0) (σ X1)
               grind)
            | exact resolve b5e19 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e54 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e23
               have i₂ := b5e18 (σ x) X0
               grind)
            | (have i₁ := b5e23
               have i₂ := b5e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b5e18 b5e23
            | (have j1 := b5e18 (σ x) X0
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | exact resolve b5e23 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e92 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k X0 (τ X1))
               have i₂ := b5e27 X1 X0
               grind)
            | exact superpose b5e27 b5e14
            | exact resolve b5e14 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27
          have b5e167 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b5e54 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e54
          have b5e168 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e167
               have r₂ := b5e24
               grind)
            | exact resolve b5e167 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e167
          have b5e169 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e168
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e168
            | exact resolve b5e168 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e168
          have b5e170 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e169
               have i₂ := b5e42
               grind)
            | exact superpose b5e42 b5e169
            | exact resolve b5e169 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42 b5e169
          have b5e171 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e170
               grind)
            | exact superpose b5e170 b5e20
            | exact resolve b5e20 b5e170
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e176 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e171
               have i₂ := b5e32 x
               grind)
            | exact superpose b5e32 b5e171
            | exact resolve b5e171 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e171
          have b5e254 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e17 (σ X0) (σ X1)
               have i₂ := b5e48 X0 X1
               grind)
            | exact superpose b5e48 b5e17
            | (have j0 := b5e17 (σ X0) (σ X1)
               have j1 := b5e48 X0 X1
               grind)
            | (have r₁ := b5e17 (σ X1) (σ X1)
               have r₂ := b5e48 X1 X1
               grind)
            | (have r₁ := b5e17 (σ X0) (σ X1)
               have r₂ := b5e48 X0 X1
               grind)
            | exact resolve b5e17 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48
          have b5e260 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e254 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e254
          have b5e261 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e260 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e260
          have b5e273 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e261 X0 X1
               have i₂ := b5e19 X0 X1
               grind)
            | exact superpose b5e19 b5e261
            | (have j0 := b5e261 X0 X1
               grind)
            | exact resolve b5e261 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e261
          have b5e4720 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            grind
          clear b5e273
          have b5e4757 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e4720 X0 X1
               have i₂ := b5e19 X1 X0
               grind)
            | exact superpose b5e19 b5e4720
            | (have j0 := b5e4720 X0 X1
               grind)
            | exact resolve b5e4720 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4720
          have b5e4758 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e4757 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4757
          have b5e7631 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e4758 X0 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e4758
            | exact resolve b5e4758 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e7734 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e7631 X0 X1
               have i₂ := b5e26 X0 X1
               grind)
            | exact superpose b5e26 b5e7631
            | (have j0 := b5e7631 X0 X1
               grind)
            | exact resolve b5e7631 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7631
          have b5e7739 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e7734 X0 X1
               have i₂ := b5e26 X0 X1
               grind)
            | exact superpose b5e26 b5e7734
            | (have j0 := b5e7734 X0 X1
               grind)
            | exact resolve b5e7734 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e7734
          have b5e11414 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e7739 X0 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e7739
            | exact resolve b5e7739 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7739
          have b5e12307 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e11414 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11414
          have b5e13107 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 (M.op X1 X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e12307 X0 (M.op X1 X1)
               have i₂ := b5e30 X1 X0
               grind)
            | exact superpose b5e30 b5e12307
            | (have j0 := b5e12307 X0 X1
               grind)
            | exact resolve b5e12307 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e12307
          have b5e14780 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (M.op (σ y) (σ y))) := by
            first
            | (have i₁ := b5e13107 (σ x) (σ y)
               have i₂ := b5e170
               grind)
            | exact superpose b5e170 b5e13107
            | (have j0 := b5e13107 (σ x) (σ y)
               grind)
            | (have r₁ := b5e13107 (σ x) (σ y)
               have r₂ := b5e170
               grind)
            | exact resolve b5e13107 b5e170
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e13107
          have b5e14810 : (σ x) = (k (σ x) (M.op (σ y) (σ y))) := by grind
          clear b5e14780
          have b5e15303 : (k x (τ (M.op (σ y) (σ y)))) = (τ (σ x)) := by
            first
            | (have i₁ := b5e92 x (M.op (σ y) (σ y))
               have i₂ := b5e14810
               grind)
            | exact superpose b5e14810 b5e92
            | exact resolve b5e92 b5e14810
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e92 b5e14810
          have b5e15328 : x = (k x (τ (M.op (σ y) (σ y)))) := by
            first
            | (have i₁ := b5e15303
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e15303
            | exact resolve b5e15303 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e15303
          have b5e16108 : x = (k x (τ (σ (k y y)))) ∨ (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b5e15328
               have i₂ := b5e4758 y y
               grind)
            | exact superpose b5e4758 b5e15328
            | (have j1 := b5e4758 y y
               grind)
            | exact resolve b5e15328 b5e4758
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4758 b5e15328
          have b5e16144 : x = (k x (k y y)) ∨ (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b5e16108
               have i₂ := b5e14 (k y y)
               grind)
            | exact superpose b5e14 b5e16108
            | exact resolve b5e16108 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16108
          have b5e24066 : x = (k x (M.op y y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e16144
               have i₂ := b5e18 y y
               grind)
            | exact superpose b5e18 b5e16144
            | (have j1 := b5e18 y y
               grind)
            | exact resolve b5e16144 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16144
          have b5e24087 : x = (k x (M.op y y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
          clear b5e24066
          have b5e24093 : x = (k x (M.op y x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e24087
               have i₂ := b5e32 y
               grind)
            | exact superpose b5e32 b5e24087
            | exact resolve b5e24087 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e24087
          have b5e24099 : x = (k x x) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e24093
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e24093
            | exact resolve b5e24093 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e24093
          have b5e24105 : (σ y) = (σ (M.op y x)) ∨ x = (k x x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e24099
               have i₂ := b5e32 y
               grind)
            | exact superpose b5e32 b5e24099
            | exact resolve b5e24099 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e24099
          have b5e24111 : (σ x) = (σ y) ∨ x = (k x x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e24105
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e24105
            | exact resolve b5e24105 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e24105
          have b5e24116 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (k x x) := by
            first
            | (have i₁ := b5e24111
               have i₂ := b5e32 y
               grind)
            | exact superpose b5e32 b5e24111
            | exact resolve b5e24111 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32 b5e24111
          have b5e24119 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by
            first
            | (have i₁ := b5e24116
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e24116
            | exact resolve b5e24116 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e24116
          have b5e24409 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
            first
            | (have i₁ := b5e18 x x
               have i₂ := b5e24119
               grind)
            | exact superpose b5e24119 b5e18
            | (have j0 := b5e18 x x
               grind)
            | exact resolve b5e18 b5e24119
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e24119
          have b5e24418 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
          clear b5e24409
          have b5e24684 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
            first
            | (have i₁ := b5e176
               have i₂ := b5e24418
               grind)
            | exact superpose b5e24418 b5e176
            | exact resolve b5e176 b5e24418
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e176 b5e24418
          have b5e24730 : (σ x) = (σ y) ∨ x = y := by grind
          clear b5e24684
          have b5e24746 : y = (τ (σ x)) ∨ x = y := by
            first
            | (have i₁ := b5e14 y
               have i₂ := b5e24730
               grind)
            | exact superpose b5e24730 b5e14
            | exact resolve b5e14 b5e24730
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e24730
          have b5e24867 : x = y ∨ x = y := by
            first
            | (have i₁ := b5e24746
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e24746
            | exact resolve b5e24746 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e24746
          have b5e24868 : x = y := by grind
          clear b5e24867
          have b5e25180 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e24868
               grind)
            | exact superpose b5e24868 b5e24
            | exact resolve b5e24 b5e24868
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e25185 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e170
               have i₂ := b5e24868
               grind)
            | exact superpose b5e24868 b5e170
            | exact resolve b5e170 b5e24868
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e170 b5e24868
          have b5e25207 : False := by grind
          exact b5e25207
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : x ≠ (M.op y x) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e24 : (σ x) = (k (σ x) (σ y)) := by grind
        have b6e25 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b6e24
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e24
          | exact resolve b6e24 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24
        have b6e42 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X1 X0 (M.op X0 x)
             have i₂ := b6e12 X0 X0 x
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e44 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e42 (σ x) X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e42
          | exact resolve b6e42 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42
        have b6e57 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e44 (σ x)
             grind)
          | exact superpose b6e44 b6e19
          | exact resolve b6e19 b6e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e44
        have b6e64 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e57
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e57
          | exact resolve b6e57 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e57
        have b6e72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X0 X1
             have i₂ := b6e17 (σ X0) (σ X1)
             grind)
          | exact superpose b6e17 b6e18
          | (have j1 := b6e17 (σ X0) (σ X1)
             grind)
          | exact resolve b6e18 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e75 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
          first
          | (have i₁ := b6e25
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e25
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e25 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e87 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
          first
          | (have r₁ := b6e75
             have r₂ := b6e20
             grind)
          | exact resolve b6e75 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e75
        have b6e93 : (σ (M.op x y)) = (σ x) := by
          first
          | (have r₁ := b6e87
             have r₂ := b6e21
             grind)
          | exact resolve b6e87 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e87
        have b6e146 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b6e64
             have i₂ := b6e93
             grind)
          | exact superpose b6e93 b6e64
          | exact resolve b6e64 b6e93
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64 b6e93
        have b6e312 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e72 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e72
          | exact resolve b6e72 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e72
        have b6e362 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) := by grind
        clear b6e312
        have b6e380 : (σ y) = (σ (k x x)) := by
          first
          | (have r₁ := b6e362
             have r₂ := b6e146
             grind)
          | exact resolve b6e362 b6e146
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e362
        have b6e417 : (k x x) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e380
             grind)
          | exact superpose b6e380 b6e13
          | exact resolve b6e13 b6e380
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e437 : y = (k x x) := by
          first
          | (have i₁ := b6e417
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e417
          | exact resolve b6e417 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e417
        have b6e497 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e437
             grind)
          | exact superpose b6e437 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e437
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e437
        have b6e498 : y = (M.op x x) ∨ x = (M.op x x) := by grind
        clear b6e497
        have b6e500 : x = (M.op x x) := by
          first
          | (have r₁ := b6e498
             have r₂ := b6e20
             grind)
          | exact resolve b6e498 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e498
        have b6e547 : x = (k x x) := by grind
        clear b6e500
        have b6e734 : (σ x) = (σ y) := by
          first
          | (have i₁ := b6e380
             have i₂ := b6e547
             grind)
          | exact superpose b6e547 b6e380
          | exact resolve b6e380 b6e547
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e380 b6e547
        have b6e745 : False := by grind
        exact b6e745
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : x ≠ (M.op y x) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e28 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) (σ x))) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ y) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e30 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X1 X0 (M.op X0 x)
               have i₂ := b7e13 X0 X0 x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e32 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e28 X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e28
            | exact resolve b7e28 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28
          have b7e36 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op X0 X0) X0)) := by
            intro X0
            grind
          clear b7e30
          have b7e40 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e17 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e17
            | (have j0 := b7e17 (σ x) (σ y)
               grind)
            | (have r₁ := b7e17 (σ x) (σ y)
               have r₂ := b7e24
               grind)
            | exact resolve b7e17 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e43 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e40
          have b7e46 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e43
               have r₂ := b7e23
               grind)
            | exact resolve b7e43 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e43
          have b7e47 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e46
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e46
            | exact resolve b7e46 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e50 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e47
               grind)
            | exact superpose b7e47 b7e14
            | exact resolve b7e14 b7e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e51 : x = (k x y) := by
            first
            | (have i₁ := b7e50
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e50
            | exact resolve b7e50 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e19 X0 X1
               have i₂ := b7e18 (σ X0) (σ X1)
               grind)
            | exact superpose b7e18 b7e19
            | (have j1 := b7e18 (σ X0) (σ X1)
               grind)
            | exact resolve b7e19 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e59 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b7e47
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e47
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e47 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
          have b7e69 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
            first
            | (have r₁ := b7e59
               have r₂ := b7e21
               grind)
            | exact resolve b7e59 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e59
          have b7e72 : (σ (M.op x y)) = (σ x) := by
            first
            | (have r₁ := b7e69
               have r₂ := b7e22
               grind)
            | exact resolve b7e69 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69
          have b7e74 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e51
               grind)
            | exact superpose b7e51 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51
          have b7e75 : x = (M.op x y) ∨ x = (M.op y x) := by
            first
            | (have r₁ := b7e74
               have r₂ := b7e21
               grind)
            | exact resolve b7e74 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e74
          have b7e77 : x = (M.op x y) := by
            first
            | (have r₁ := b7e75
               have r₂ := b7e22
               grind)
            | exact resolve b7e75 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e75
          have b7e80 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e32 (σ x)
               grind)
            | exact superpose b7e32 b7e20
            | exact resolve b7e20 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e90 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e80
               have i₂ := b7e72
               grind)
            | exact superpose b7e72 b7e80
            | exact resolve b7e80 b7e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72 b7e80
          have b7e288 : ∀ X0 : G, (σ y) = (M.op (σ X0) (σ x)) ∨ (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e32 (σ X0)
               have i₂ := b7e58 y X0
               grind)
            | exact superpose b7e58 b7e32
            | (have j1 := b7e58 y X0
               grind)
            | exact resolve b7e32 b7e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e294 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e58 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58
          have b7e295 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e294 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e294
          have b7e312 : ∀ X0 : G, (σ X0) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ X0) (σ x)) ∨ (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e288 X0
               have i₂ := b7e32 (σ y)
               grind)
            | exact superpose b7e32 b7e288
            | (have j0 := b7e288 X0
               grind)
            | exact resolve b7e288 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e288
          have b7e351 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (σ x) := by
            intro X0
            first
            | (have i₁ := b7e312 X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e312
            | (have j0 := b7e312 X0
               grind)
            | exact resolve b7e312 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e312
          have b7e2432 : (M.op (σ y) (σ x)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e32 (σ y)
               have i₂ := b7e351 y
               grind)
            | exact superpose b7e351 b7e32
            | (have j1 := b7e351 y
               grind)
            | exact resolve b7e32 b7e351
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32 b7e351
          have b7e2495 : (σ x) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e2432
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e2432
            | exact resolve b7e2432 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2432
          have b7e2535 : (σ x) = (σ y) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e2495
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e2495
            | exact resolve b7e2495 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2495
          have b7e2536 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
          clear b7e2535
          have b7e2569 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e2536
               grind)
            | exact superpose b7e2536 b7e14
            | exact resolve b7e14 b7e2536
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e2607 : x = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e2569
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e2569
            | exact resolve b7e2569 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2569
          have b7e2755 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e18 y y
               have i₂ := b7e2607
               grind)
            | exact superpose b7e2607 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e2607
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2607
          have b7e2756 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b7e2755
          have b7e7244 : y = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b7e2756
          have b7e7864 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e2536
               have i₂ := b7e7244
               grind)
            | exact superpose b7e7244 b7e2536
            | exact resolve b7e2536 b7e7244
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2536 b7e7244
          have b7e7885 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b7e7864
          have b7e8279 : x = (k x (M.op x y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e36 y
               have i₂ := b7e7885
               grind)
            | exact superpose b7e7885 b7e36
            | exact resolve b7e36 b7e7885
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36 b7e7885
          have b7e8312 : x = (k x x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e8279
               have i₂ := b7e77
               grind)
            | exact superpose b7e77 b7e8279
            | exact resolve b7e8279 b7e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77 b7e8279
          have b7e8886 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e295 x
               have i₂ := b7e8312
               grind)
            | exact superpose b7e8312 b7e295
            | (have j0 := b7e295 x
               grind)
            | exact resolve b7e295 b7e8312
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e295 b7e8312
          have b7e8905 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
          clear b7e8886
          have b7e8911 : (σ x) = (σ y) := by
            first
            | (have r₁ := b7e8905
               have r₂ := b7e90
               grind)
            | exact resolve b7e8905 b7e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e8905
          have b7e9082 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e8911
               grind)
            | exact superpose b7e8911 b7e24
            | exact resolve b7e24 b7e8911
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e8911
          have b7e9178 : False := by grind
          exact b7e9178
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x x) := by grind
          have b8e22 : x ≠ (M.op y x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e60 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 (σ x) X0
               grind)
            | (have i₁ := b8e23
               have i₂ := b8e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b8e18 b8e23
            | (have j1 := b8e18 (σ x) X0
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e117 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b8e60 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60
          have b8e118 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e117
               have r₂ := b8e24
               grind)
            | exact resolve b8e117 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e117
          have b8e119 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e118
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e118
            | exact resolve b8e118 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e118
          have b8e156 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e119
               grind)
            | exact superpose b8e119 b8e20
            | exact resolve b8e20 b8e119
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e119
          have b8e271 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e156
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e156
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e156 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e156
          have b8e272 : y = (M.op x x) ∨ x = (M.op y x) := by grind
          clear b8e271
          have b8e274 : x = (M.op y x) := by
            first
            | (have r₁ := b8e272
               have r₂ := b8e21
               grind)
            | exact resolve b8e272 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e272
          have b8e276 : False := by grind
          exact b8e276

/-- `Equation3331`: `x ◇ y = x ◇ (z ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_x_pxy_Equation3331 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3331 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3331.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (x) (y) with h0a | h0a
  · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = y := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e27 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
        intro X0
        grind
      have b0e28 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        grind
      clear b0e27
      have b0e76 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e80 : False := by grind
      exact b0e80
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
      · have b1e20 : x = y := by grind
        have b1e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e27 : False := by grind
        exact b1e27
      · have b2e20 : x = y := by grind
        have b2e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e27 : False := by grind
        exact b2e27
  · rcases eq_or_ne (M.op x x) (M.op x y) with h0b | h0b
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e20 : x ≠ y := by grind
        have b3e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e26 : y = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 y
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e13
          | exact resolve b3e13 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e27 : x = y := by
          first
          | (have i₁ := b3e26
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e26
          | exact resolve b3e26 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26
        have b3e28 : False := by grind
        exact b3e28
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : (M.op x y) = (M.op x x) := by grind
          have b4e24 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e26 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e27 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e26
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e26
            | exact resolve b4e26 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26
          have b4e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e32 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e31
          have b4e60 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e27
               have i₂ := b4e32 x
               grind)
            | exact superpose b4e32 b4e27
            | (have r₁ := b4e27
               have r₂ := b4e32 x
               grind)
            | exact resolve b4e27 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27 b4e32
          have b4e62 : False := by grind
          exact b4e62
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X1 X2))) := by
            intro X0 X1 X2
            grind
          have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : x ≠ y := by grind
          have b5e22 : (M.op x y) = (M.op x x) := by grind
          have b5e23 : (σ x) ≠ (σ y) := by grind
          have b5e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e26 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e20
            | exact resolve b5e20 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e30
          have b5e40 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op y (M.op x x))) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 x y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e42 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X2 X1 (M.op X0 X1)
               have i₂ := b5e13 (M.op X0 X1) X0 X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e58 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ x = (k x y) := by
            first
            | (have i₁ := b5e17 x y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e17
            | (have j0 := b5e17 x y
               grind)
            | (have r₁ := b5e17 x y
               have r₂ := b5e22
               grind)
            | exact resolve b5e17 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e63 : x = y ∨ x = (k x y) := by grind
          clear b5e58
          have b5e64 : x = (k x y) := by
            first
            | (have r₁ := b5e63
               have r₂ := b5e21
               grind)
            | exact resolve b5e63 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63
          have b5e72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X0 X1
               have i₂ := b5e18 (σ X0) (σ X1)
               grind)
            | exact superpose b5e18 b5e19
            | (have j1 := b5e18 (σ X0) (σ X1)
               grind)
            | exact resolve b5e19 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e72 X0 X1
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e72
            | (have j0 := b5e72 X0 X1
               grind)
            | exact resolve b5e72 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e72
          have b5e102 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) x)) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 y (M.op x x)
               have i₂ := b5e40 (M.op x x)
               grind)
            | exact superpose b5e40 b5e13
            | exact resolve b5e13 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40
          have b5e108 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e102 X0
               have i₂ := b5e42 x x X0
               grind)
            | exact superpose b5e42 b5e102
            | exact resolve b5e102 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e102
          have b5e111 : ∀ X0 : G, (M.op y X0) ≠ (M.op y x) ∨ y = X0 ∨ y = (k y X0) := by
            intro X0
            first
            | (have i₁ := b5e17 y X0
               have i₂ := b5e108 y
               grind)
            | exact superpose b5e108 b5e17
            | (have j0 := b5e17 y X0
               grind)
            | (have r₁ := b5e17 y x
               have r₂ := b5e108 y
               grind)
            | (have r₁ := b5e17 x y
               have r₂ := b5e108 x
               grind)
            | exact resolve b5e17 b5e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e108
          have b5e123 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e42 (σ X0) (σ X0) X1
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e42
            | exact resolve b5e42 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31
          have b5e763 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (M.op X2 (M.op (σ X1) (σ (k X0 X1)))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X2 (σ X0) (σ X1)
               have i₂ := b5e85 X0 X1
               grind)
            | exact superpose b5e85 b5e13
            | (have j1 := b5e85 X0 X1
               grind)
            | exact resolve b5e13 b5e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e788 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ (M.op X0 X0)) (σ X0))) = (M.op X1 (σ X2)) ∨ (M.op (σ X0) (σ X2)) = (σ (k X0 X2)) ∨ (σ X0) = (σ X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e42 (σ X0) (σ X2) X1
               have i₂ := b5e85 X0 X2
               grind)
            | exact superpose b5e85 b5e42
            | (have j1 := b5e85 X0 X2
               grind)
            | exact resolve b5e42 b5e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42 b5e85
          have b5e815 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X2)) = (σ (k X0 X2)) ∨ (M.op X1 (σ X0)) = (M.op X1 (σ X2)) ∨ (σ X0) = (σ X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e788 X0 X1 X2
               have i₂ := b5e123 X0 X1
               grind)
            | exact superpose b5e123 b5e788
            | (have j0 := b5e788 X0 X1 X2
               grind)
            | exact resolve b5e788 b5e123
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e123 b5e788
          have b5e4606 : x = y ∨ y = (k y x) := by
            first
            | (have j0 := b5e111 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e111
          have b5e4610 : y = (k y x) := by
            first
            | (have r₁ := b5e4606
               have r₂ := b5e21
               grind)
            | exact resolve b5e4606 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4606
          have b5e46540 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) (σ x))) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b5e763 x y X0
               have i₂ := b5e64
               grind)
            | exact superpose b5e64 b5e763
            | (have j0 := b5e763 x y x
               grind)
            | exact resolve b5e763 b5e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e64 b5e763
          have b5e47272 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) (σ x))) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have j0 := b5e46540 X0
               grind)
            | (have r₁ := b5e46540 X0
               have r₂ := b5e26
               grind)
            | exact resolve b5e46540 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e46540
          have b5e47318 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) (σ x))) := by
            intro X0
            first
            | (have j0 := b5e47272 X0
               grind)
            | (have r₁ := b5e47272 X0
               have r₂ := b5e23
               grind)
            | exact resolve b5e47272 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47272
          have b5e47345 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (σ (k y x))) ∨ (M.op X1 (σ y)) = (M.op X1 (σ x)) ∨ (σ x) = (σ y) := by
            intro X0 X1
            first
            | (have i₁ := b5e47318 X0
               have i₂ := b5e815 y X1 x
               grind)
            | exact superpose b5e815 b5e47318
            | (have j1 := b5e815 y X1 x
               grind)
            | exact resolve b5e47318 b5e815
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e815 b5e47318
          have b5e47751 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (σ (k y x))) ∨ (M.op X1 (σ y)) = (M.op X1 (σ x)) := by
            intro X0 X1
            first
            | (have j0 := b5e47345 X0 X1
               grind)
            | (have r₁ := b5e47345 X0 X1
               have r₂ := b5e23
               grind)
            | exact resolve b5e47345 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47345
          have b5e47824 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (M.op X1 (σ y)) = (M.op X1 (σ x)) := by
            intro X0 X1
            first
            | (have i₁ := b5e47751 X0 X1
               have i₂ := b5e4610
               grind)
            | exact superpose b5e4610 b5e47751
            | (have j0 := b5e47751 X0 X0
               grind)
            | exact resolve b5e47751 b5e4610
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4610 b5e47751
          have b5e90186 : ∀ X0 : G, (M.op X0 (σ x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have j0 := b5e47824 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47824
          have b5e90187 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have j0 := b5e90186 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e90186
          have b5e91888 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e90187 (σ x)
               grind)
            | exact superpose b5e90187 b5e24
            | (have r₁ := b5e24
               have r₂ := b5e90187 (σ x)
               grind)
            | exact resolve b5e24 b5e90187
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e90187
          have b5e91922 : False := by grind
          exact b5e91922
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e20 : x ≠ y := by grind
        have b6e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e25 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e13
          | exact resolve b6e13 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e26 : x = y := by
          first
          | (have i₁ := b6e25
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e25
          | exact resolve b6e25 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e27 : False := by grind
        exact b6e27
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X1 X2))) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : (M.op x y) ≠ (M.op x x) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e30
          have b7e41 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X2 X1 (M.op X0 X1)
               have i₂ := b7e13 (M.op X0 X1) X0 X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e61 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e17 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e17
            | (have j0 := b7e17 (σ x) (σ y)
               grind)
            | (have r₁ := b7e17 (σ x) (σ y)
               have r₂ := b7e24
               grind)
            | exact resolve b7e17 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e63 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (σ X0) = (k (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e17 (σ X0) X1
               have i₂ := b7e31 X0
               grind)
            | exact superpose b7e31 b7e17
            | (have j0 := b7e17 (σ X0) X1
               grind)
            | exact resolve b7e17 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e65 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e61
          have b7e66 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e65
               have r₂ := b7e23
               grind)
            | exact resolve b7e65 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e67 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e66
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e66
            | exact resolve b7e66 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e71 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e67
               grind)
            | exact superpose b7e67 b7e14
            | exact resolve b7e14 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e72 : x = (k x y) := by
            first
            | (have i₁ := b7e71
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e71
            | exact resolve b7e71 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e90 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X2 (M.op X0 (M.op X0 X1))) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X2 X0 X0
               have i₂ := b7e18 X0 X1
               grind)
            | (have i₁ := b7e13 X0 X0 X1
               have i₂ := b7e18 X0 X1
               grind)
            | exact superpose b7e18 b7e13
            | (have j1 := b7e18 X0 X1
               grind)
            | exact resolve b7e13 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e101 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e72
               grind)
            | exact superpose b7e72 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72
          have b7e102 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e101
               have r₂ := b7e22
               grind)
            | exact resolve b7e101 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e101
          have b7e104 : x = (M.op x y) := by
            first
            | (have r₁ := b7e102
               have r₂ := b7e21
               grind)
            | exact resolve b7e102 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e102
          have b7e110 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ x)) (σ x))) := by
            intro X0
            first
            | (have i₁ := b7e41 (σ x) (σ y) X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e41
            | exact resolve b7e41 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e122 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e110 X0
               have i₂ := b7e41 (σ x) (σ x) X0
               grind)
            | exact superpose b7e41 b7e110
            | exact resolve b7e110 b7e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41 b7e110
          have b7e130 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op y x)) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 x y
               have i₂ := b7e104
               grind)
            | exact superpose b7e104 b7e13
            | exact resolve b7e13 b7e104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e104
          have b7e315 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e31 y
               have i₂ := b7e122 (σ y)
               grind)
            | exact superpose b7e122 b7e31
            | exact resolve b7e31 b7e122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31 b7e122
          have b7e398 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y x)) ∨ (M.op y x) = (k y x) ∨ x = y := by
            intro X0
            first
            | (have i₁ := b7e90 y x X0
               have i₂ := b7e130 y
               grind)
            | exact superpose b7e130 b7e90
            | (have j0 := b7e90 y x x
               grind)
            | exact resolve b7e90 b7e130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90
          have b7e421 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y x)) ∨ (M.op y x) = (k y x) := by
            intro X0
            first
            | (have j0 := b7e398 X0
               grind)
            | (have r₁ := b7e398 X0
               have r₂ := b7e21
               grind)
            | exact resolve b7e398 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e398
          have b7e423 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (M.op y x) = (k y x) := by
            intro X0
            first
            | (have i₁ := b7e421 X0
               have i₂ := b7e130 X0
               grind)
            | exact superpose b7e130 b7e421
            | exact resolve b7e421 b7e130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e421
          have b7e9546 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b7e63 y (σ x)
               have i₂ := b7e315
               grind)
            | exact superpose b7e315 b7e63
            | (have j0 := b7e63 x (σ y)
               grind)
            | (have r₁ := b7e63 y (σ x)
               have r₂ := b7e315
               grind)
            | exact resolve b7e63 b7e315
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63 b7e315
          have b7e9593 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by grind
          clear b7e9546
          have b7e9600 : (σ y) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b7e9593
               have r₂ := b7e23
               grind)
            | exact resolve b7e9593 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e9593
          have b7e9619 : (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b7e9600
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e9600
            | exact resolve b7e9600 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e9600
          have b7e9640 : (k y x) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k y x)
               have i₂ := b7e9619
               grind)
            | exact superpose b7e9619 b7e14
            | exact resolve b7e14 b7e9619
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e9619
          have b7e9684 : y = (k y x) := by
            first
            | (have i₁ := b7e9640
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e9640
            | exact resolve b7e9640 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e9640
          have b7e9755 : ∀ X0 : G, y = (M.op y x) ∨ (M.op X0 y) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b7e423 X0
               have i₂ := b7e9684
               grind)
            | exact superpose b7e9684 b7e423
            | (have j0 := b7e423 X0
               grind)
            | exact resolve b7e423 b7e9684
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e423 b7e9684
          have b7e11001 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 x) ∨ (M.op X1 x) = (M.op X1 y) := by
            intro X0 X1
            first
            | (have i₁ := b7e130 X0
               have i₂ := b7e9755 X1
               grind)
            | exact superpose b7e9755 b7e130
            | (have j1 := b7e9755 X0
               grind)
            | exact resolve b7e130 b7e9755
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e130 b7e9755
          have b7e13124 : ∀ X0 : G, (M.op X0 x) ≠ (M.op X0 x) ∨ (M.op X0 y) = (M.op X0 x) := by
            intro X0
            first
            | (have j0 := b7e11001 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e11001
          have b7e13125 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
            intro X0
            first
            | (have j0 := b7e13124 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e13124
          have b7e14467 : (M.op x x) ≠ (M.op x x) := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e13125 x
               grind)
            | exact superpose b7e13125 b7e22
            | (have r₁ := b7e22
               have r₂ := b7e13125 x
               grind)
            | exact resolve b7e22 b7e13125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e13125
          have b7e14472 : False := by grind
          exact b7e14472
        · have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : (M.op x y) ≠ (M.op x x) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e29
          have b8e79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e18 (σ X0) (σ X1)
               grind)
            | exact superpose b8e18 b8e19
            | (have j1 := b8e18 (σ X0) (σ X1)
               grind)
            | exact resolve b8e19 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e79 X0 X1
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e79
            | (have j0 := b8e79 X0 X1
               grind)
            | exact resolve b8e79 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e79
          have b8e730 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e91 x y
               grind)
            | exact superpose b8e91 b8e20
            | (have j1 := b8e91 x y
               grind)
            | exact resolve b8e20 b8e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e91
          have b8e799 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e730
               have r₂ := b8e23
               grind)
            | exact resolve b8e730 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e730
          have b8e5147 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b8e799
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e799
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e799
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e799
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e799 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e799
          have b8e5148 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
          clear b8e5147
          have b8e5153 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = y := by
            first
            | (have r₁ := b8e5148
               have r₂ := b8e22
               grind)
            | exact resolve b8e5148 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5148
          have b8e5158 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e5153
               have r₂ := b8e21
               grind)
            | exact resolve b8e5153 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5153
          have b8e5164 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e5158
               grind)
            | exact superpose b8e5158 b8e24
            | exact resolve b8e24 b8e5158
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5158
          have b8e5218 : False := by grind
          exact b8e5218

/-- `Equation3331`: `x ◇ y = x ◇ (z ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_x_pyx_Equation3331 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3331 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3331.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (x) (y) with h0a | h0a
  · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = y := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e27 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
        intro X0
        grind
      have b0e28 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        grind
      clear b0e27
      have b0e77 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e81 : False := by grind
      exact b0e81
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
      · have b1e20 : x = y := by grind
        have b1e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e27 : False := by grind
        exact b1e27
      · have b2e20 : x = y := by grind
        have b2e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e27 : False := by grind
        exact b2e27
  · rcases eq_or_ne (M.op x x) (M.op x y) with h0b | h0b
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e20 : x ≠ y := by grind
        have b3e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e26 : y = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 y
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e13
          | exact resolve b3e13 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e27 : x = y := by
          first
          | (have i₁ := b3e26
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e26
          | exact resolve b3e26 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26
        have b3e28 : False := by grind
        exact b3e28
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : (M.op x y) = (M.op x x) := by grind
          have b4e24 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e26 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e27 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e26
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e26
            | exact resolve b4e26 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26
          have b4e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e32 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e31
          have b4e60 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e27
               have i₂ := b4e32 x
               grind)
            | exact superpose b4e32 b4e27
            | (have r₁ := b4e27
               have r₂ := b4e32 x
               grind)
            | exact resolve b4e27 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27 b4e32
          have b4e62 : False := by grind
          exact b4e62
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X1 X2))) := by
            intro X0 X1 X2
            grind
          have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : x ≠ y := by grind
          have b5e22 : (M.op x y) = (M.op x x) := by grind
          have b5e23 : (σ x) ≠ (σ y) := by grind
          have b5e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e26 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e20
            | exact resolve b5e20 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e30
          have b5e40 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op y (M.op x x))) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 x y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e42 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X2 X1 (M.op X0 X1)
               have i₂ := b5e13 (M.op X0 X1) X0 X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e57 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ X0) (σ (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 (σ X0) (σ X0)
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e13
            | exact resolve b5e13 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e58 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ x = (k x y) := by
            first
            | (have i₁ := b5e17 x y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e17
            | (have j0 := b5e17 x y
               grind)
            | (have r₁ := b5e17 x y
               have r₂ := b5e22
               grind)
            | exact resolve b5e17 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e63 : x = y ∨ x = (k x y) := by grind
          clear b5e58
          have b5e64 : x = (k x y) := by
            first
            | (have r₁ := b5e63
               have r₂ := b5e21
               grind)
            | exact resolve b5e63 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63
          have b5e72 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X1 X0
               have i₂ := b5e18 (σ X1) (σ X0)
               grind)
            | exact superpose b5e18 b5e19
            | (have j1 := b5e18 (σ X1) (σ X0)
               grind)
            | exact resolve b5e19 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e79 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X2 (M.op X0 (M.op X0 X1))) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X2 X0 X0
               have i₂ := b5e18 X0 X1
               grind)
            | (have i₁ := b5e13 X0 X0 X1
               have i₂ := b5e18 X0 X1
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X0 X1
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e85 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e72 X0 X1
               have i₂ := b5e31 X1
               grind)
            | exact superpose b5e31 b5e72
            | (have j0 := b5e72 X0 X1
               grind)
            | exact resolve b5e72 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e72
          have b5e103 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) x)) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 y (M.op x x)
               have i₂ := b5e40 (M.op x x)
               grind)
            | exact superpose b5e40 b5e13
            | exact resolve b5e13 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40
          have b5e110 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e103 X0
               have i₂ := b5e42 x x X0
               grind)
            | exact superpose b5e42 b5e103
            | exact resolve b5e103 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42 b5e103
          have b5e113 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ y = X0 ∨ y = (k y X0) := by
            intro X0
            first
            | (have i₁ := b5e17 y X0
               have i₂ := b5e110 y
               grind)
            | exact superpose b5e110 b5e17
            | (have j0 := b5e17 y X0
               grind)
            | (have r₁ := b5e17 y x
               have r₂ := b5e110 y
               grind)
            | (have r₁ := b5e17 x y
               have r₂ := b5e110 x
               grind)
            | exact resolve b5e17 b5e110
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e110
          have b5e627 : ∀ X0 X1 X2 : G, (M.op X2 (σ X1)) = (M.op X2 (M.op (σ X0) (σ (k X0 X1)))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X2 (σ X1) (σ X0)
               have i₂ := b5e85 X1 X0
               grind)
            | exact superpose b5e85 b5e13
            | (have j1 := b5e85 X1 X0
               grind)
            | exact resolve b5e13 b5e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e85
          have b5e4765 : x = y ∨ y = (k y x) := by
            first
            | (have j0 := b5e113 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e113
          have b5e4769 : y = (k y x) := by
            first
            | (have r₁ := b5e4765
               have r₂ := b5e21
               grind)
            | exact resolve b5e4765 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4765
          have b5e45818 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b5e627 x y X0
               have i₂ := b5e64
               grind)
            | exact superpose b5e64 b5e627
            | (have j0 := b5e627 x y x
               grind)
            | exact resolve b5e627 b5e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e64 b5e627
          have b5e46175 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have j0 := b5e45818 X0
               grind)
            | (have r₁ := b5e45818 X0
               have r₂ := b5e26
               grind)
            | exact resolve b5e45818 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e45818
          have b5e46218 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ x))) := by
            intro X0
            first
            | (have j0 := b5e46175 X0
               grind)
            | (have r₁ := b5e46175 X0
               have r₂ := b5e23
               grind)
            | exact resolve b5e46175 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46175
          have b5e46230 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x x))) := by
            intro X0
            first
            | (have i₁ := b5e46218 X0
               have i₂ := b5e31 x
               grind)
            | exact superpose b5e31 b5e46218
            | exact resolve b5e46218 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31 b5e46218
          have b5e46430 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ x) (σ y))) := by
            intro X0
            first
            | (have i₁ := b5e57 x X0
               have i₂ := b5e46230 (σ x)
               grind)
            | exact superpose b5e46230 b5e57
            | exact resolve b5e57 b5e46230
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e57 b5e46230
          have b5e47564 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) (σ x))) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 (σ x) (σ y)
               have i₂ := b5e46430 (σ y)
               grind)
            | exact superpose b5e46430 b5e13
            | exact resolve b5e13 b5e46430
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e48563 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b5e79 (σ y) (σ x) X0
               have i₂ := b5e47564 (σ y)
               grind)
            | exact superpose b5e47564 b5e79
            | (have j0 := b5e79 (σ y) (σ x) x
               grind)
            | exact resolve b5e79 b5e47564
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e79
          have b5e48907 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ y) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            intro X0
            first
            | (have j0 := b5e48563 X0
               grind)
            | (have r₁ := b5e48563 X0
               have r₂ := b5e23
               grind)
            | exact resolve b5e48563 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48563
          have b5e48989 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e48907 X0
               have i₂ := b5e47564 X0
               grind)
            | exact superpose b5e47564 b5e48907
            | exact resolve b5e48907 b5e47564
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47564 b5e48907
          have b5e49029 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e48989 X0
               have i₂ := b5e19 y x
               grind)
            | exact superpose b5e19 b5e48989
            | (have j0 := b5e48989 X0
               grind)
            | exact resolve b5e48989 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48989
          have b5e49044 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e49029 X0
               have i₂ := b5e4769
               grind)
            | exact superpose b5e4769 b5e49029
            | (have j0 := b5e49029 X0
               grind)
            | exact resolve b5e49029 b5e4769
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4769 b5e49029
          have b5e70167 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e49044 (σ x)
               grind)
            | exact superpose b5e49044 b5e24
            | (have r₁ := b5e24
               have r₂ := b5e49044 (σ x)
               grind)
            | exact resolve b5e24 b5e49044
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49044
          have b5e70177 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b5e70167
          have b5e70355 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e46430 X0
               have i₂ := b5e70177
               grind)
            | exact superpose b5e70177 b5e46430
            | exact resolve b5e46430 b5e70177
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46430 b5e70177
          have b5e72557 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e70355 (σ x)
               grind)
            | exact superpose b5e70355 b5e24
            | (have r₁ := b5e24
               have r₂ := b5e70355 (σ x)
               grind)
            | exact resolve b5e24 b5e70355
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e70355
          have b5e72585 : False := by grind
          exact b5e72585
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e20 : x ≠ y := by grind
        have b6e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e25 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e13
          | exact resolve b6e13 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e26 : x = y := by
          first
          | (have i₁ := b6e25
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e25
          | exact resolve b6e25 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e27 : False := by grind
        exact b6e27
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X1 X2))) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : (M.op x y) ≠ (M.op x x) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e20
            | exact resolve b7e20 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e30
          have b7e41 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X2 X1 (M.op X0 X1)
               have i₂ := b7e13 (M.op X0 X1) X0 X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e58 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e26
               have i₂ := b7e31 x
               grind)
            | exact superpose b7e31 b7e26
            | exact resolve b7e26 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26
          have b7e61 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e17 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e17
            | (have j0 := b7e17 (σ x) (σ y)
               grind)
            | (have r₁ := b7e17 (σ x) (σ y)
               have r₂ := b7e24
               grind)
            | exact resolve b7e17 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e63 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (σ X0) = (k (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e17 (σ X0) X1
               have i₂ := b7e31 X0
               grind)
            | exact superpose b7e31 b7e17
            | (have j0 := b7e17 (σ X0) X1
               grind)
            | exact resolve b7e17 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e65 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e61
          have b7e66 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e65
               have r₂ := b7e23
               grind)
            | exact resolve b7e65 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e67 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e66
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e66
            | exact resolve b7e66 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e71 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e67
               grind)
            | exact superpose b7e67 b7e14
            | exact resolve b7e14 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e72 : x = (k x y) := by
            first
            | (have i₁ := b7e71
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e71
            | exact resolve b7e71 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e90 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X2 (M.op X0 (M.op X0 X1))) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X2 X0 X0
               have i₂ := b7e18 X0 X1
               grind)
            | (have i₁ := b7e13 X0 X0 X1
               have i₂ := b7e18 X0 X1
               grind)
            | exact superpose b7e18 b7e13
            | (have j1 := b7e18 X0 X1
               grind)
            | exact resolve b7e13 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e102 : x = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e72
               grind)
            | exact superpose b7e72 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72
          have b7e103 : x = (M.op y x) ∨ x = y := by
            first
            | (have r₁ := b7e102
               have r₂ := b7e22
               grind)
            | exact resolve b7e102 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e102
          have b7e105 : x = (M.op y x) := by
            first
            | (have r₁ := b7e103
               have r₂ := b7e21
               grind)
            | exact resolve b7e103 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e103
          have b7e111 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ x)) (σ x))) := by
            intro X0
            first
            | (have i₁ := b7e41 (σ x) (σ y) X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e41
            | exact resolve b7e41 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e124 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e111 X0
               have i₂ := b7e41 (σ x) (σ x) X0
               grind)
            | exact superpose b7e41 b7e111
            | exact resolve b7e111 b7e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e111
          have b7e129 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b7e41 y x X0
               have i₂ := b7e105
               grind)
            | exact superpose b7e105 b7e41
            | exact resolve b7e41 b7e105
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41
          have b7e237 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e31 y
               have i₂ := b7e124 (σ y)
               grind)
            | exact superpose b7e124 b7e31
            | exact resolve b7e31 b7e124
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31 b7e124
          have b7e320 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y x)) ∨ (M.op x y) = (k y x) ∨ x = y := by
            intro X0
            first
            | (have i₁ := b7e90 y x X0
               have i₂ := b7e105
               grind)
            | exact superpose b7e105 b7e90
            | (have j0 := b7e90 y x x
               grind)
            | exact resolve b7e90 b7e105
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90
          have b7e352 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y x)) ∨ (M.op x y) = (k y x) := by
            intro X0
            first
            | (have j0 := b7e320 X0
               grind)
            | (have r₁ := b7e320 X0
               have r₂ := b7e21
               grind)
            | exact resolve b7e320 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e320
          have b7e357 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) ∨ (M.op x y) = (k y x) := by
            intro X0
            first
            | (have i₁ := b7e352 X0
               have i₂ := b7e105
               grind)
            | exact superpose b7e105 b7e352
            | exact resolve b7e352 b7e105
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e105 b7e352
          have b7e9812 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b7e63 y (σ x)
               have i₂ := b7e237
               grind)
            | exact superpose b7e237 b7e63
            | (have j0 := b7e63 x (σ y)
               grind)
            | (have r₁ := b7e63 y (σ x)
               have r₂ := b7e237
               grind)
            | exact resolve b7e63 b7e237
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63 b7e237
          have b7e9859 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by grind
          clear b7e9812
          have b7e9866 : (σ y) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b7e9859
               have r₂ := b7e23
               grind)
            | exact resolve b7e9859 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e9859
          have b7e9886 : (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b7e9866
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e9866
            | exact resolve b7e9866 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e9866
          have b7e9907 : (k y x) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k y x)
               have i₂ := b7e9886
               grind)
            | exact superpose b7e9886 b7e14
            | exact resolve b7e14 b7e9886
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e9886
          have b7e9953 : y = (k y x) := by
            first
            | (have i₁ := b7e9907
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e9907
            | exact resolve b7e9907 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e9907
          have b7e10063 : ∀ X0 : G, y = (M.op x y) ∨ (M.op X0 x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e357 X0
               have i₂ := b7e9953
               grind)
            | exact superpose b7e9953 b7e357
            | (have j0 := b7e357 X0
               grind)
            | exact resolve b7e357 b7e9953
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e357 b7e9953
          have b7e11806 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e58
               have i₂ := b7e10063 x
               grind)
            | exact superpose b7e10063 b7e58
            | exact resolve b7e58 b7e10063
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e10063
          have b7e11819 : y = (M.op x y) := by grind
          clear b7e11806
          have b7e12511 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e129 X0
               have i₂ := b7e11819
               grind)
            | exact superpose b7e11819 b7e129
            | exact resolve b7e129 b7e11819
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e129 b7e11819
          have b7e14426 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e58
               have i₂ := b7e12511 x
               grind)
            | exact superpose b7e12511 b7e58
            | exact resolve b7e58 b7e12511
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58 b7e12511
          have b7e14440 : False := by grind
          exact b7e14440
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X1 X2))) := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : (M.op x y) ≠ (M.op x x) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 (τ X0)
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e19
            | exact resolve b8e19 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e29
          have b8e40 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X2 X1 (M.op X0 X1)
               have i₂ := b8e13 (M.op X0 X1) X0 X1
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e79 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e18 (σ X1) (σ X0)
               grind)
            | exact superpose b8e18 b8e19
            | (have j1 := b8e18 (σ X1) (σ X0)
               grind)
            | exact resolve b8e19 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e81 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e17 X0 X1
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e17 X0 X0
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e17
            | (have j0 := b8e17 X0 X1
               have j1 := b8e18 X0 X1
               grind)
            | (have r₁ := b8e17 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e17 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | (have r₁ := b8e17 X0 X1
               have r₂ := b8e18 (M.op X0 X1) (M.op X0 X0)
               grind)
            | exact resolve b8e17 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e88 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e81 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e81
          have b8e89 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e88 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e88
          have b8e91 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e79 X0 X1
               have i₂ := b8e30 X1
               grind)
            | exact superpose b8e30 b8e79
            | (have j0 := b8e79 X0 X1
               grind)
            | exact resolve b8e79 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e79
          have b8e109 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X2 (M.op (M.op X0 X1) X0)) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e40 X0 X0 X2
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e40 X0 X1 X2
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e40
            | (have j1 := b8e18 X0 X1
               grind)
            | exact resolve b8e40 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e110 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e40 (σ X0) (σ X0) X1
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e40
            | exact resolve b8e40 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30
          have b8e122 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X1) = (M.op X2 X0) ∨ X0 = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e109 X0 X1 X2
               have i₂ := b8e40 X0 X1 X2
               grind)
            | exact superpose b8e40 b8e109
            | (have j0 := b8e109 X0 X1 X2
               grind)
            | exact resolve b8e109 b8e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e109
          have b8e213 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e89 (σ X0) (σ X1)
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e89
            | (have j0 := b8e89 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
               grind)
            | exact resolve b8e89 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e216 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 ∨ (τ X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e27 X0 X1
               have i₂ := b8e89 X1 (τ X0)
               grind)
            | exact superpose b8e89 b8e27
            | (have j1 := b8e89 X1 (τ X0)
               grind)
            | exact resolve b8e27 b8e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27
          have b8e221 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e89 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e89
          have b8e584 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ (M.op X0 X0)) (σ X0))) = (M.op X1 (σ X2)) ∨ (σ (k X0 X2)) = (M.op (σ X2) (σ X0)) ∨ (σ X0) = (σ X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e40 (σ X0) (σ X2) X1
               have i₂ := b8e91 X2 X0
               grind)
            | exact superpose b8e91 b8e40
            | (have j1 := b8e91 X2 X0
               grind)
            | exact resolve b8e40 b8e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40 b8e91
          have b8e610 : ∀ X0 X1 X2 : G, (σ (k X0 X2)) = (M.op (σ X2) (σ X0)) ∨ (M.op X1 (σ X0)) = (M.op X1 (σ X2)) ∨ (σ X0) = (σ X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e584 X0 X1 X2
               have i₂ := b8e110 X0 X1
               grind)
            | exact superpose b8e110 b8e584
            | (have j0 := b8e584 X0 X1 X2
               grind)
            | exact resolve b8e584 b8e110
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e110 b8e584
          have b8e6264 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e216 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e216
            | exact resolve b8e216 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e216
          have b8e6338 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e6264 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e6264
            | (have j0 := b8e6264 X0 X1
               grind)
            | exact resolve b8e6264 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6264
          have b8e8550 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e213 y x
               grind)
            | exact superpose b8e213 b8e20
            | (have j1 := b8e213 y x
               grind)
            | exact resolve b8e20 b8e213
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e213
          have b8e8627 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have r₁ := b8e8550
               have r₂ := b8e23
               grind)
            | exact resolve b8e8550 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8550
          have b8e8661 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k y x) ∨ x = y := by
            first
            | (have i₁ := b8e8627
               have i₂ := b8e6338 x y
               grind)
            | exact superpose b8e6338 b8e8627
            | (have j1 := b8e6338 x y
               grind)
            | (have r₁ := b8e8627
               have r₂ := b8e6338 x y
               grind)
            | (have r₁ := b8e8627
               have r₂ := b8e6338 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e8627
               have r₂ := b8e6338 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e8627 b8e6338
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6338 b8e8627
          have b8e8662 : (σ (M.op x y)) = (σ y) ∨ y = (k y x) ∨ x = y := by grind
          clear b8e8661
          have b8e8668 : (σ (M.op x y)) = (σ y) ∨ y = (k y x) := by
            first
            | (have r₁ := b8e8662
               have r₂ := b8e21
               grind)
            | exact resolve b8e8662 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8662
          have b8e8812 : (M.op x y) = (τ (σ y)) ∨ y = (k y x) := by
            first
            | (have i₁ := b8e14 (M.op x y)
               have i₂ := b8e8668
               grind)
            | exact superpose b8e8668 b8e14
            | exact resolve b8e14 b8e8668
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8668
          have b8e8864 : y = (k y x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e8812
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e8812
            | exact resolve b8e8812 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8812
          have b8e9827 : ∀ X0 : G, y = (M.op x y) ∨ (M.op X0 x) = (M.op X0 y) ∨ x = y ∨ y = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e122 y x X0
               have i₂ := b8e8864
               grind)
            | exact superpose b8e8864 b8e122
            | (have j0 := b8e122 y x X0
               grind)
            | exact resolve b8e122 b8e8864
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e122 b8e8864
          have b8e9834 : ∀ X0 : G, y = (M.op x y) ∨ (M.op X0 x) = (M.op X0 y) ∨ x = y := by
            intro X0
            first
            | (have j0 := b8e9827 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9827
          have b8e9843 : ∀ X0 : G, y = (M.op x y) ∨ (M.op X0 x) = (M.op X0 y) := by
            intro X0
            first
            | (have j0 := b8e9834 X0
               grind)
            | (have r₁ := b8e9834 X0
               have r₂ := b8e21
               grind)
            | exact resolve b8e9834 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9834
          have b8e10612 : (M.op x x) ≠ (M.op x x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e22
               have i₂ := b8e9843 x
               grind)
            | exact superpose b8e9843 b8e22
            | (have r₁ := b8e22
               have r₂ := b8e9843 x
               grind)
            | exact resolve b8e22 b8e9843
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9843
          have b8e10614 : y = (M.op x y) := by grind
          clear b8e10612
          have b8e10748 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b8e20
               have i₂ := b8e610 y X0 x
               grind)
            | exact superpose b8e610 b8e20
            | (have j1 := b8e610 x X0 y
               grind)
            | exact resolve b8e20 b8e610
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e610
          have b8e11115 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b8e10748 X0
               grind)
            | (have r₁ := b8e10748 X0
               have r₂ := b8e23
               grind)
            | exact resolve b8e10748 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10748
          have b8e11150 : ∀ X0 : G, (σ y) ≠ (σ (k y x)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e11115 X0
               have i₂ := b8e10614
               grind)
            | exact superpose b8e10614 b8e11115
            | (have j0 := b8e11115 X0
               grind)
            | exact resolve b8e11115 b8e10614
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11115
          have b8e11189 : y ≠ y ∨ y = (k y x) ∨ x = y := by
            first
            | (have i₁ := b8e221 y x
               have i₂ := b8e10614
               grind)
            | exact superpose b8e10614 b8e221
            | (have j0 := b8e221 y x
               grind)
            | (have r₁ := b8e221 y x
               have r₂ := b8e10614
               grind)
            | exact resolve b8e221 b8e10614
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e221 b8e10614
          have b8e11194 : y = (k y x) ∨ x = y := by grind
          clear b8e11189
          have b8e11195 : y = (k y x) := by
            first
            | (have r₁ := b8e11194
               have r₂ := b8e21
               grind)
            | exact resolve b8e11194 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11194
          have b8e27519 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e11150 X0
               have i₂ := b8e11195
               grind)
            | exact superpose b8e11195 b8e11150
            | (have j0 := b8e11150 X0
               grind)
            | exact resolve b8e11150 b8e11195
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11150 b8e11195
          have b8e27530 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b8e27519 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27519
          have b8e28465 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e27530 (σ x)
               grind)
            | exact superpose b8e27530 b8e24
            | (have r₁ := b8e24
               have r₂ := b8e27530 (σ x)
               grind)
            | exact resolve b8e24 b8e27530
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27530
          have b8e28472 : False := by grind
          exact b8e28472
