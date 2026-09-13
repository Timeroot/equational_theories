import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2700`: `x = ((y ◇ x) ◇ (x ◇ y)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_pyx_pyx_pxx_pyx_Equation2700 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2700 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2700.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (M.op x y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op x y) = (M.op x x) := by grind
      have b0e20 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e18
        | exact resolve b0e18 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e22 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e21
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e21
        | exact resolve b0e21 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21
      have b0e45 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e51 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e45 (σ X0)
           grind)
        | exact superpose b0e45 b0e17
        | exact resolve b0e17 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e56 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e51 X0
           have i₂ := b0e45 X0
           grind)
        | exact superpose b0e45 b0e51
        | exact resolve b0e51 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45 b0e51
      have b0e207 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e56 x
           grind)
        | exact superpose b0e56 b0e22
        | (have r₁ := b0e22
           have r₂ := b0e56 x
           grind)
        | exact resolve b0e22 b0e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e56
      have b0e217 : False := by grind
      exact b0e217
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) (M.op X0 X1)) X1) = X0 := by
          intro X0 X1
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : (M.op x y) = (M.op x x) := by grind
        have b1e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e26 : y = (M.op (M.op (M.op x x) (M.op y x)) x) := by
          first
          | (have i₁ := b1e12 y x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e52 : (M.op x x) ≠ (M.op x x) ∨ (M.op y x) = (k x y) := by
          first
          | (have i₁ := b1e15 x y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e15
          | (have j0 := b1e15 x x
             grind)
          | (have r₁ := b1e15 x y
             have r₂ := b1e20
             grind)
          | exact resolve b1e15 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e54 : (M.op y x) = (k x y) := by grind
        clear b1e52
        have b1e56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e53 (σ X0)
             grind)
          | exact superpose b1e53 b1e18
          | exact resolve b1e18 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e63 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e56 X0
             have i₂ := b1e53 X0
             grind)
          | exact superpose b1e53 b1e56
          | exact resolve b1e56 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53 b1e56
        have b1e70 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e16 (σ x) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e16
          | (have j0 := b1e16 (σ x) (σ y)
             grind)
          | (have r₁ := b1e16 (σ x) (σ y)
             have r₂ := b1e22
             grind)
          | exact resolve b1e16 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e72 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b1e70
        have b1e73 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e72
             have r₂ := b1e21
             grind)
          | exact resolve b1e72 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e72
        have b1e74 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e73
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e73
          | exact resolve b1e73 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e73
        have b1e75 : (M.op (σ x) (σ x)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b1e74
             have i₂ := b1e54
             grind)
          | exact superpose b1e54 b1e74
          | exact resolve b1e74 b1e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54 b1e74
        have b1e76 : (σ (M.op x x)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b1e75
             have i₂ := b1e63 x
             grind)
          | exact superpose b1e63 b1e75
          | exact resolve b1e75 b1e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e63 b1e75
        have b1e140 : (M.op y x) = (τ (σ (M.op x x))) := by
          first
          | (have i₁ := b1e13 (M.op y x)
             have i₂ := b1e76
             grind)
          | exact superpose b1e76 b1e13
          | exact resolve b1e13 b1e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e76
        have b1e141 : (M.op x x) = (M.op y x) := by
          first
          | (have i₁ := b1e140
             have i₂ := b1e13 (M.op x x)
             grind)
          | exact superpose b1e13 b1e140
          | exact resolve b1e140 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e140
        have b1e152 : y = (M.op (M.op (M.op x x) (M.op x x)) x) := by
          first
          | (have i₁ := b1e26
             have i₂ := b1e141
             grind)
          | exact superpose b1e141 b1e26
          | exact resolve b1e26 b1e141
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e141
        have b1e159 : x = y := by
          first
          | (have i₁ := b1e152
             have i₂ := b1e12 x x
             grind)
          | exact superpose b1e12 b1e152
          | exact resolve b1e152 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e152
        have b1e173 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e159
             grind)
          | exact superpose b1e159 b1e21
          | exact resolve b1e21 b1e159
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e159
        have b1e178 : False := by grind
        exact b1e178
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op x y) = (M.op x x) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e23 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e19
          | exact resolve b2e19 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e77 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X0 X1
             have i₂ := b2e17 X0 X1
             grind)
          | (have i₁ := b2e15 X0 X0
             have i₂ := b2e17 X0 X1
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X0 X0
             have j1 := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X1 X1
             have r₂ := b2e17 X1 X1
             grind)
          | (have r₁ := b2e15 X0 X0
             have r₂ := b2e17 X0 X0
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e86 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e16 X0 X1
             have i₂ := b2e17 X0 X1
             grind)
          | (have i₁ := b2e16 X0 X0
             have i₂ := b2e17 X0 X1
             grind)
          | exact superpose b2e17 b2e16
          | (have j0 := b2e16 X0 X1
             have j1 := b2e17 X0 X1
             grind)
          | (have r₁ := b2e16 X0 X0
             have r₂ := b2e17 X0 X0
             grind)
          | (have r₁ := b2e16 X1 X1
             have r₂ := b2e17 X1 X1
             grind)
          | (have r₁ := b2e16 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | exact resolve b2e16 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e103 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b2e86 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e86
        have b2e104 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b2e103 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e103
        have b2e106 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e77 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e77
        have b2e107 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e106 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e106
        have b2e119 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b2e104 X0 X1
             have j1 := b2e15 X0 X1
             grind)
          | (have r₁ := b2e104 X0 X1
             have r₂ := b2e15 X0 X1
             grind)
          | (have r₁ := b2e104 X1 X1
             have r₂ := b2e15 X1 X1
             grind)
          | exact resolve b2e104 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e104
        have b2e353 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b2e119 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e119
        have b2e360 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b2e353 X0 X1
             have j1 := b2e107 X0 X1
             grind)
          | (have r₁ := b2e353 X0 X1
             have r₂ := b2e107 X0 X1
             grind)
          | (have r₁ := b2e353 X1 X1
             have r₂ := b2e107 X1 X1
             grind)
          | exact resolve b2e353 b2e107
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e107 b2e353
        have b2e401 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e360 (σ X1) (σ X0)
             grind)
          | exact superpose b2e360 b2e18
          | exact resolve b2e18 b2e360
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e408 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e401 X0 X1
             have i₂ := b2e360 X1 X0
             grind)
          | exact superpose b2e360 b2e401
          | exact resolve b2e401 b2e360
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e360 b2e401
        have b2e615 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e23
             have i₂ := b2e408 x y
             grind)
          | exact superpose b2e408 b2e23
          | exact resolve b2e23 b2e408
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23 b2e408
        have b2e647 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e615
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e615
          | exact resolve b2e615 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e615
        have b2e648 : False := by grind
        exact b2e648
  · rcases eq_or_ne (M.op x x) (M.op y x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b3e21 : (M.op x x) = (M.op y x) := by grind
        have b3e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e19
          | exact resolve b3e19 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e52 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b3e15 (σ x) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e15
          | (have j0 := b3e15 (σ x) (σ x)
             grind)
          | (have r₁ := b3e15 (σ x) (σ y)
             have r₂ := b3e22
             grind)
          | exact resolve b3e15 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e54 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b3e52
        have b3e55 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e54
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e54
          | exact resolve b3e54 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54
        have b3e57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 X0
             have i₂ := b3e53 (σ X0)
             grind)
          | exact superpose b3e53 b3e18
          | exact resolve b3e18 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e64 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e57 X0
             have i₂ := b3e53 X0
             grind)
          | exact superpose b3e53 b3e57
          | exact resolve b3e57 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53 b3e57
        have b3e70 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
          first
          | (have i₁ := b3e16 x y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e16
          | (have j0 := b3e16 x y
             grind)
          | (have r₁ := b3e16 x y
             have r₂ := b3e21
             grind)
          | exact resolve b3e16 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e73 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by grind
        clear b3e70
        have b3e74 : (M.op x x) = (k x y) := by
          first
          | (have r₁ := b3e73
             have r₂ := b3e20
             grind)
          | exact resolve b3e73 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e73
        have b3e84 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e15 X0 X1
             have i₂ := b3e17 X0 X1
             grind)
          | (have i₁ := b3e15 X0 X0
             have i₂ := b3e17 X0 X1
             grind)
          | exact superpose b3e17 b3e15
          | (have j0 := b3e15 X0 X0
             have j1 := b3e17 X0 X1
             grind)
          | (have r₁ := b3e15 X0 X1
             have r₂ := b3e17 X0 X1
             grind)
          | (have r₁ := b3e15 X1 X1
             have r₂ := b3e17 X1 X1
             grind)
          | (have r₁ := b3e15 X0 X0
             have r₂ := b3e17 X0 X0
             grind)
          | exact resolve b3e15 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e94 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e16 X0 X1
             have i₂ := b3e17 X0 X1
             grind)
          | (have i₁ := b3e16 X0 X0
             have i₂ := b3e17 X0 X1
             grind)
          | exact superpose b3e17 b3e16
          | (have j0 := b3e16 X0 X1
             have j1 := b3e17 X0 X1
             grind)
          | (have r₁ := b3e16 X0 X0
             have r₂ := b3e17 X0 X0
             grind)
          | (have r₁ := b3e16 X1 X1
             have r₂ := b3e17 X1 X1
             grind)
          | (have r₁ := b3e16 X0 X1
             have r₂ := b3e17 X0 X1
             grind)
          | exact resolve b3e16 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e111 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b3e17 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e114 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b3e94 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e94
        have b3e115 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b3e114 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e114
        have b3e117 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e84 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e84
        have b3e118 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e117 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e117
        have b3e120 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b3e111 X0 X1
             have j1 := b3e15 X0 X1
             grind)
          | (have r₁ := b3e111 X0 X1
             have r₂ := b3e15 X0 X1
             grind)
          | (have r₁ := b3e111 X1 X1
             have r₂ := b3e15 X1 X1
             grind)
          | exact resolve b3e111 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e111
        have b3e132 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b3e115 X0 X1
             have j1 := b3e15 X0 X1
             grind)
          | (have r₁ := b3e115 X0 X1
             have r₂ := b3e15 X0 X1
             grind)
          | (have r₁ := b3e115 X1 X1
             have r₂ := b3e15 X1 X1
             grind)
          | exact resolve b3e115 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e115
        have b3e256 : (M.op (σ x) (σ y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b3e120 (σ y) (σ x)
             have i₂ := b3e55
             grind)
          | exact superpose b3e55 b3e120
          | (have j0 := b3e120 (σ y) (σ x)
             grind)
          | exact resolve b3e120 b3e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e55 b3e120
        have b3e270 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b3e256
             have i₂ := b3e74
             grind)
          | exact superpose b3e74 b3e256
          | exact resolve b3e256 b3e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e74 b3e256
        have b3e276 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b3e270
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e270
          | exact resolve b3e270 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e270
        have b3e279 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have r₁ := b3e276
             have r₂ := b3e64 x
             grind)
          | exact resolve b3e276 b3e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e64 b3e276
        have b3e280 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b3e279
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e279
          | exact resolve b3e279 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e279
        have b3e333 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b3e132 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e132
        have b3e340 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b3e333 X0 X1
             have j1 := b3e118 X0 X1
             grind)
          | (have r₁ := b3e333 X0 X1
             have r₂ := b3e118 X0 X1
             grind)
          | (have r₁ := b3e333 X1 X1
             have r₂ := b3e118 X1 X1
             grind)
          | exact resolve b3e333 b3e118
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e118 b3e333
        have b3e437 : (M.op (σ x) (σ x)) = (σ (k y x)) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e280
             grind)
          | exact superpose b3e280 b3e22
          | exact resolve b3e22 b3e280
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e280
        have b3e443 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e437
             have i₂ := b3e340 y x
             grind)
          | exact superpose b3e340 b3e437
          | exact resolve b3e437 b3e340
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e340 b3e437
        have b3e447 : False := by grind
        exact b3e447
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e103 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X0 X1
               have i₂ := b4e18 X0 X1
               grind)
            | (have i₁ := b4e16 X0 X0
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e16
            | (have j0 := b4e16 X0 X0
               have j1 := b4e18 X0 X1
               grind)
            | (have r₁ := b4e16 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e16 X1 X1
               have r₂ := b4e18 X1 X1
               grind)
            | (have r₁ := b4e16 X0 X0
               have r₂ := b4e18 X0 X0
               grind)
            | exact resolve b4e16 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e112 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 X0 X1
               have i₂ := b4e18 X0 X1
               grind)
            | (have i₁ := b4e17 X0 X0
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e17
            | (have j0 := b4e17 X0 X1
               have j1 := b4e18 X0 X1
               grind)
            | (have r₁ := b4e17 X0 X0
               have r₂ := b4e18 X0 X0
               grind)
            | (have r₁ := b4e17 X1 X1
               have r₂ := b4e18 X1 X1
               grind)
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | exact resolve b4e17 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e132 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e112 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e112
          have b4e133 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e132 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e132
          have b4e135 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e103 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e103
          have b4e136 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e135 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e135
          have b4e150 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e133 X0 X1
               have j1 := b4e16 X0 X1
               grind)
            | (have r₁ := b4e133 X0 X1
               have r₂ := b4e16 X0 X1
               grind)
            | (have r₁ := b4e133 X1 X1
               have r₂ := b4e16 X1 X1
               grind)
            | exact resolve b4e133 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e133
          have b4e374 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e150 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e150
          have b4e381 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e374 X0 X1
               have j1 := b4e136 X0 X1
               grind)
            | (have r₁ := b4e374 X0 X1
               have r₂ := b4e136 X0 X1
               grind)
            | (have r₁ := b4e374 X1 X1
               have r₂ := b4e136 X1 X1
               grind)
            | exact resolve b4e374 b4e136
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e136 b4e374
          have b4e442 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 X0
               have i₂ := b4e381 (σ X1) (σ X0)
               grind)
            | exact superpose b4e381 b4e19
            | exact resolve b4e19 b4e381
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e450 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e442 X0 X1
               have i₂ := b4e381 X1 X0
               grind)
            | exact superpose b4e381 b4e442
            | exact resolve b4e442 b4e381
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e381 b4e442
          have b4e684 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e450 x y
               grind)
            | exact superpose b4e450 b4e20
            | (have r₁ := b4e20
               have r₂ := b4e450 x y
               grind)
            | exact resolve b4e20 b4e450
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e450
          have b4e707 : False := by grind
          exact b4e707
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e96 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e16 X0 X1
               have i₂ := b5e18 X0 X1
               grind)
            | (have i₁ := b5e16 X0 X0
               have i₂ := b5e18 X0 X1
               grind)
            | exact superpose b5e18 b5e16
            | (have j0 := b5e16 X0 X0
               have j1 := b5e18 X0 X1
               grind)
            | (have r₁ := b5e16 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | (have r₁ := b5e16 X1 X1
               have r₂ := b5e18 X1 X1
               grind)
            | (have r₁ := b5e16 X0 X0
               have r₂ := b5e18 X0 X0
               grind)
            | exact resolve b5e16 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e105 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e17 X0 X1
               have i₂ := b5e18 X0 X1
               grind)
            | (have i₁ := b5e17 X0 X0
               have i₂ := b5e18 X0 X1
               grind)
            | exact superpose b5e18 b5e17
            | (have j0 := b5e17 X0 X1
               have j1 := b5e18 X0 X1
               grind)
            | (have r₁ := b5e17 X0 X0
               have r₂ := b5e18 X0 X0
               grind)
            | (have r₁ := b5e17 X1 X1
               have r₂ := b5e18 X1 X1
               grind)
            | (have r₁ := b5e17 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | exact resolve b5e17 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e125 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b5e105 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e105
          have b5e126 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b5e125 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e125
          have b5e128 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e96 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e96
          have b5e129 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e128 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e128
          have b5e143 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b5e126 X0 X1
               have j1 := b5e16 X0 X1
               grind)
            | (have r₁ := b5e126 X0 X1
               have r₂ := b5e16 X0 X1
               grind)
            | (have r₁ := b5e126 X1 X1
               have r₂ := b5e16 X1 X1
               grind)
            | exact resolve b5e126 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e126
          have b5e365 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b5e143 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e143
          have b5e372 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b5e365 X0 X1
               have j1 := b5e129 X0 X1
               grind)
            | (have r₁ := b5e365 X0 X1
               have r₂ := b5e129 X0 X1
               grind)
            | (have r₁ := b5e365 X1 X1
               have r₂ := b5e129 X1 X1
               grind)
            | exact resolve b5e365 b5e129
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e129 b5e365
          have b5e442 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X1 X0
               have i₂ := b5e372 (σ X1) (σ X0)
               grind)
            | exact superpose b5e372 b5e19
            | exact resolve b5e19 b5e372
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e450 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e442 X0 X1
               have i₂ := b5e372 X1 X0
               grind)
            | exact superpose b5e372 b5e442
            | exact resolve b5e442 b5e372
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e372 b5e442
          have b5e662 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e450 x y
               grind)
            | exact superpose b5e450 b5e20
            | (have r₁ := b5e20
               have r₂ := b5e450 x y
               grind)
            | exact resolve b5e20 b5e450
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e450
          have b5e686 : False := by grind
          exact b5e686
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e24 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 (τ X0) X1
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e18
          | exact resolve b6e18 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b6e13 (k (τ X0) X1)
             have i₂ := b6e24 X0 X1
             grind)
          | exact superpose b6e24 b6e13
          | exact resolve b6e13 b6e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24
        have b6e85 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e15 X0 X1
             have i₂ := b6e17 X0 X1
             grind)
          | (have i₁ := b6e15 X0 X0
             have i₂ := b6e17 X0 X1
             grind)
          | exact superpose b6e17 b6e15
          | (have j0 := b6e15 X0 X0
             have j1 := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X1 X1
             have r₂ := b6e17 X1 X1
             grind)
          | (have r₁ := b6e15 X0 X0
             have r₂ := b6e17 X0 X0
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e95 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e16 X0 X1
             have i₂ := b6e17 X0 X1
             grind)
          | (have i₁ := b6e16 X0 X0
             have i₂ := b6e17 X0 X1
             grind)
          | exact superpose b6e17 b6e16
          | (have j0 := b6e16 X0 X1
             have j1 := b6e17 X0 X1
             grind)
          | (have r₁ := b6e16 X0 X0
             have r₂ := b6e17 X0 X0
             grind)
          | (have r₁ := b6e16 X1 X1
             have r₂ := b6e17 X1 X1
             grind)
          | (have r₁ := b6e16 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | exact resolve b6e16 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e113 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b6e95 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e95
        have b6e114 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b6e113 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e113
        have b6e116 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e85 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e85
        have b6e117 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e116 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e116
        have b6e130 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b6e114 X0 X1
             have j1 := b6e15 X0 X1
             grind)
          | (have r₁ := b6e114 X0 X1
             have r₂ := b6e15 X0 X1
             grind)
          | (have r₁ := b6e114 X1 X1
             have r₂ := b6e15 X1 X1
             grind)
          | exact resolve b6e114 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e114
        have b6e284 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b6e130 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e130
        have b6e291 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b6e284 X0 X1
             have j1 := b6e117 X0 X1
             grind)
          | (have r₁ := b6e284 X0 X1
             have r₂ := b6e117 X0 X1
             grind)
          | (have r₁ := b6e284 X1 X1
             have r₂ := b6e117 X1 X1
             grind)
          | exact resolve b6e284 b6e117
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e117 b6e284
        have b6e318 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e29 X1 X0
             have i₂ := b6e291 X1 (σ X0)
             grind)
          | exact superpose b6e291 b6e29
          | exact resolve b6e29 b6e291
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e29
        have b6e321 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e318 X0 X1
             have i₂ := b6e291 (τ X1) X0
             grind)
          | exact superpose b6e291 b6e318
          | exact resolve b6e318 b6e291
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e291 b6e318
        have b6e568 : (M.op x (τ (σ y))) = (τ (M.op (σ x) (σ x))) := by
          first
          | (have i₁ := b6e321 x (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e321
          | exact resolve b6e321 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e592 : (M.op x (τ (σ y))) = (M.op x (τ (σ x))) := by
          first
          | (have i₁ := b6e568
             have i₂ := b6e321 x (σ x)
             grind)
          | exact superpose b6e321 b6e568
          | exact resolve b6e568 b6e321
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e321 b6e568
        have b6e601 : (M.op x x) = (M.op x (τ (σ y))) := by
          first
          | (have i₁ := b6e592
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e592
          | exact resolve b6e592 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e592
        have b6e604 : (M.op x y) = (M.op x x) := by
          first
          | (have i₁ := b6e601
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e601
          | exact resolve b6e601 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e601
        have b6e605 : False := by grind
        exact b6e605
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b7e22 : (M.op x x) ≠ (M.op y x) := by grind
          have b7e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e63 (σ X0)
               grind)
            | exact superpose b7e63 b7e19
            | exact resolve b7e19 b7e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e74 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e65 X0
               have i₂ := b7e63 X0
               grind)
            | exact superpose b7e63 b7e65
            | exact resolve b7e65 b7e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63 b7e65
          have b7e83 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
          have b7e85 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e83
          have b7e86 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e85
               have r₂ := b7e23
               grind)
            | exact resolve b7e85 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e85
          have b7e87 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e86
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e86
            | exact resolve b7e86 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e86
          have b7e88 : (σ (k x y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e87
               have i₂ := b7e74 x
               grind)
            | exact superpose b7e74 b7e87
            | exact resolve b7e87 b7e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e74 b7e87
          have b7e93 : (k x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e88
               grind)
            | exact superpose b7e88 b7e14
            | exact resolve b7e14 b7e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e88
          have b7e94 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b7e93
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e93
            | exact resolve b7e93 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e93
          have b7e166 : (M.op x x) = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e94
               grind)
            | exact superpose b7e94 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e94
          have b7e167 : (M.op x x) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by grind
          clear b7e166
          have b7e169 : (M.op x y) = (M.op x x) := by
            first
            | (have r₁ := b7e167
               have r₂ := b7e22
               grind)
            | exact resolve b7e167 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e167
          have b7e171 : False := by grind
          exact b7e171
        · have b8e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e104 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X0 X1
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e16 X0 X0
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X0 X0
               have j1 := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | (have r₁ := b8e16 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e114 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
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
            | (have r₁ := b8e17 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | (have r₁ := b8e17 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | (have r₁ := b8e17 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | exact resolve b8e17 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e133 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e114 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e114
          have b8e134 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e133 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e133
          have b8e136 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e104 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e104
          have b8e137 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e136 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e136
          have b8e151 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e134 X0 X1
               have j1 := b8e16 X0 X1
               grind)
            | (have r₁ := b8e134 X0 X1
               have r₂ := b8e16 X0 X1
               grind)
            | (have r₁ := b8e134 X1 X1
               have r₂ := b8e16 X1 X1
               grind)
            | exact resolve b8e134 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e134
          have b8e341 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e151 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e151
          have b8e348 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e341 X0 X1
               have j1 := b8e137 X0 X1
               grind)
            | (have r₁ := b8e341 X0 X1
               have r₂ := b8e137 X0 X1
               grind)
            | (have r₁ := b8e341 X1 X1
               have r₂ := b8e137 X1 X1
               grind)
            | exact resolve b8e341 b8e137
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e137 b8e341
          have b8e387 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e348 (σ X1) (σ X0)
               grind)
            | exact superpose b8e348 b8e19
            | exact resolve b8e19 b8e348
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e398 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e387 X0 X1
               have i₂ := b8e348 X1 X0
               grind)
            | exact superpose b8e348 b8e387
            | exact resolve b8e387 b8e348
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e348 b8e387
          have b8e772 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e398 x y
               grind)
            | exact superpose b8e398 b8e20
            | (have r₁ := b8e20
               have r₂ := b8e398 x y
               grind)
            | exact resolve b8e20 b8e398
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e398
          have b8e799 : False := by grind
          exact b8e799

/-- `Equation2700`: `x = ((y ◇ x) ◇ (x ◇ y)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation2700 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2700 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2700.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e37 : (M.op x y) = (k x y) := by grind
      have b0e38 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
      have b0e40 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e38
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e38
        | exact resolve b0e38 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38
      have b0e41 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e40
           have i₂ := b0e37
           grind)
        | exact superpose b0e37 b0e40
        | exact resolve b0e40 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37 b0e40
      have b0e42 : False := by grind
      exact b0e42
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e35 : (M.op x y) = (k x y) := by grind
        have b1e68 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        have b1e81 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e68
             have r₂ := b1e21
             grind)
          | exact resolve b1e68 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e68
        have b1e82 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e81
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e81
          | exact resolve b1e81 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e81
        have b1e83 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e82
             have i₂ := b1e35
             grind)
          | exact superpose b1e35 b1e82
          | exact resolve b1e82 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35 b1e82
        have b1e84 : False := by grind
        exact b1e84
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e48 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e70 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b2e71 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b2e70 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e70
        have b2e234 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e71 X0
             have i₂ := b2e48 X0 X1
             grind)
          | (have i₁ := b2e71 X0
             have i₂ := b2e48 X0 (M.op X0 X0)
             grind)
          | exact superpose b2e48 b2e71
          | (have j1 := b2e48 X1 X0
             grind)
          | exact resolve b2e71 b2e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48 b2e71
        have b2e252 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e234 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e234
        have b2e492 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e252 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e252
        have b2e493 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e492 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e492
        have b2e566 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e493 (σ X0)
             grind)
          | exact superpose b2e493 b2e18
          | exact resolve b2e18 b2e493
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e573 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e566 X0
             have i₂ := b2e493 X0
             grind)
          | exact superpose b2e493 b2e566
          | exact resolve b2e566 b2e493
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e493 b2e566
        have b2e799 : (σ y) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e573 x
             grind)
          | exact superpose b2e573 b2e21
          | exact resolve b2e21 b2e573
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e573
        have b2e830 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e799
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e799
          | exact resolve b2e799 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e799
        have b2e831 : False := by grind
        exact b2e831
  · rcases eq_or_ne (M.op y y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : x = (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e36 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        have b3e37 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e36
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e36
          | exact resolve b3e36 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e36
        have b3e67 : y = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
        have b3e79 : (M.op x y) = (k x y) := by
          first
          | (have r₁ := b3e67
             have r₂ := b3e20
             grind)
          | exact resolve b3e67 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e67
        have b3e93 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e37
             grind)
          | exact superpose b3e37 b3e19
          | exact resolve b3e19 b3e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37
        have b3e98 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b3e93
             have i₂ := b3e79
             grind)
          | exact superpose b3e79 b3e93
          | exact resolve b3e93 b3e79
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e79 b3e93
        have b3e99 : False := by grind
        exact b3e99
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : y ≠ (M.op x x) := by grind
          have b4e22 : x = (M.op y y) := by grind
          have b4e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e80 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
          have b4e81 : y = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
          have b4e93 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b4e81
               have r₂ := b4e21
               grind)
            | exact resolve b4e81 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e81
          have b4e94 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b4e80
               have r₂ := b4e23
               grind)
            | exact resolve b4e80 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e80
          have b4e95 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b4e94
               have i₂ := b4e19 x y
               grind)
            | exact superpose b4e19 b4e94
            | exact resolve b4e94 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e94
          have b4e96 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e95
               have i₂ := b4e93
               grind)
            | exact superpose b4e93 b4e95
            | exact resolve b4e95 b4e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e93 b4e95
          have b4e97 : False := by grind
          exact b4e97
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op y y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e55 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e81 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b5e82 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b5e81 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e81
          have b5e232 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e82 X0
               have i₂ := b5e55 X0 X1
               grind)
            | (have i₁ := b5e82 X0
               have i₂ := b5e55 X0 (M.op X0 X0)
               grind)
            | exact superpose b5e55 b5e82
            | (have j1 := b5e55 X1 X0
               grind)
            | exact resolve b5e82 b5e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55 b5e82
          have b5e248 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e232 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e232
          have b5e482 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e248 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e248
          have b5e483 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e482 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e482
          have b5e554 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e483 (σ X0)
               grind)
            | exact superpose b5e483 b5e19
            | exact resolve b5e19 b5e483
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e561 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e554 X0
               have i₂ := b5e483 X0
               grind)
            | exact superpose b5e483 b5e554
            | exact resolve b5e554 b5e483
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e483 b5e554
          have b5e789 : (σ x) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e561 y
               grind)
            | exact superpose b5e561 b5e24
            | exact resolve b5e24 b5e561
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e561
          have b5e819 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e789
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e789
            | exact resolve b5e789 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e789
          have b5e820 : False := by grind
          exact b5e820
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e55 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          grind
        have b6e79 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b6e80 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b6e79 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e79
        have b6e163 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e80 X0
             have i₂ := b6e55 X0 X1
             grind)
          | (have i₁ := b6e80 X0
             have i₂ := b6e55 X0 (M.op X0 X0)
             grind)
          | exact superpose b6e55 b6e80
          | (have j1 := b6e55 X1 X0
             grind)
          | exact resolve b6e80 b6e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55 b6e80
        have b6e177 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b6e163 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e163
        have b6e246 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b6e177 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e177
        have b6e275 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b6e246 (σ x) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e246
          | exact resolve b6e246 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e287 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e246 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e246
        have b6e294 : (σ y) = (k (σ x) (σ x)) := by grind
        clear b6e275
        have b6e306 : (σ y) = (σ (k x x)) := by
          first
          | (have i₁ := b6e294
             have i₂ := b6e18 x x
             grind)
          | exact superpose b6e18 b6e294
          | exact resolve b6e294 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e294
        have b6e313 : (σ y) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e306
             have i₂ := b6e287 x
             grind)
          | exact superpose b6e287 b6e306
          | exact resolve b6e306 b6e287
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e287 b6e306
        have b6e461 : (M.op x x) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (M.op x x)
             have i₂ := b6e313
             grind)
          | exact superpose b6e313 b6e13
          | exact resolve b6e13 b6e313
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e313
        have b6e462 : y = (M.op x x) := by
          first
          | (have i₁ := b6e461
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e461
          | exact resolve b6e461 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e461
        have b6e467 : False := by grind
        exact b6e467
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op y y) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e59 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            grind
          have b7e91 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b7e92 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b7e91 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e91
          have b7e156 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e92 X0
               have i₂ := b7e59 X0 X1
               grind)
            | (have i₁ := b7e92 X0
               have i₂ := b7e59 X0 (M.op X0 X0)
               grind)
            | exact superpose b7e59 b7e92
            | (have j1 := b7e59 X1 X0
               grind)
            | exact resolve b7e92 b7e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e59 b7e92
          have b7e170 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e156 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e156
          have b7e213 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e170 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e170
          have b7e258 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e213 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e213
            | exact resolve b7e213 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e268 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e213 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e213
          have b7e274 : (σ x) = (k (σ y) (σ y)) := by grind
          clear b7e258
          have b7e285 : (σ x) = (σ (k y y)) := by
            first
            | (have i₁ := b7e274
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e274
            | exact resolve b7e274 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e274
          have b7e292 : (σ x) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e285
               have i₂ := b7e268 y
               grind)
            | exact superpose b7e268 b7e285
            | exact resolve b7e285 b7e268
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e268 b7e285
          have b7e420 : (M.op y y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e292
               grind)
            | exact superpose b7e292 b7e14
            | exact resolve b7e14 b7e292
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e292
          have b7e421 : x = (M.op y y) := by
            first
            | (have i₁ := b7e420
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e420
            | exact resolve b7e420 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e420
          have b7e426 : False := by grind
          exact b7e426
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x x) := by grind
          have b8e22 : x ≠ (M.op y y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e62 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 X0) = (σ y) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 (σ y) X0
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e18 X0 (M.op (σ y) (σ y))
               grind)
            | exact superpose b8e18 b8e24
            | (have j1 := b8e18 (σ y) X0
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ y) (σ x)
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e262 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have j0 := b8e62 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62
          have b8e263 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b8e262
               have r₂ := b8e23
               grind)
            | exact resolve b8e262 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e262
          have b8e264 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e263
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e263
            | exact resolve b8e263 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e263
          have b8e265 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e264
               grind)
            | exact superpose b8e264 b8e20
            | exact resolve b8e20 b8e264
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e264
          have b8e278 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b8e265
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e265
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e265 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e265
          have b8e279 : x = (M.op y y) ∨ y = (M.op x x) := by grind
          clear b8e278
          have b8e280 : y = (M.op x x) := by
            first
            | (have r₁ := b8e279
               have r₂ := b8e22
               grind)
            | exact resolve b8e279 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e279
          have b8e282 : False := by grind
          exact b8e282

/-- `Equation2700`: `x = ((y ◇ x) ◇ (x ◇ y)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(X,X) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pyx_pxx_pyy_pyx_Equation2700 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2700 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2700.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (M.op y y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) (M.op X0 X1)) X1) = X0 := by
        intro X0 X1
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op y x) = (M.op y y) := by grind
      have b0e20 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e23 : x = (M.op (M.op (M.op y y) (M.op x y)) y) := by
        first
        | (have i₁ := b0e11 x y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41 : (M.op y y) ≠ (M.op y y) ∨ (k x y) = (M.op x x) := by
        first
        | (have i₁ := b0e14 x y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 y y
           grind)
        | (have r₁ := b0e14 x y
           have r₂ := b0e19
           grind)
        | exact resolve b0e14 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e42 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e14 (σ x) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have j0 := b0e14 (σ y) (σ y)
           grind)
        | (have r₁ := b0e14 (σ x) (σ y)
           have r₂ := b0e20
           grind)
        | exact resolve b0e14 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e43 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e44 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
      clear b0e42
      have b0e45 : (k x y) = (M.op x x) := by grind
      clear b0e41
      have b0e46 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e44
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e44
        | exact resolve b0e44 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44
      have b0e47 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b0e46
           have i₂ := b0e45
           grind)
        | exact superpose b0e45 b0e46
        | exact resolve b0e46 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45 b0e46
      have b0e49 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e43 (σ X0)
           grind)
        | exact superpose b0e43 b0e17
        | exact resolve b0e17 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e54 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e49 X0
           have i₂ := b0e43 X0
           grind)
        | exact superpose b0e43 b0e49
        | exact resolve b0e49 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43 b0e49
      have b0e77 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X0)) X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1 X0
           have i₂ := b0e16 X0 X1
           grind)
        | (have i₁ := b0e11 X0 X0
           have i₂ := b0e16 X0 X1
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X0 X1
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1118 : (σ x) = (M.op (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b0e77 (σ y) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e77
        | (have j0 := b0e77 (σ y) (σ x)
           grind)
        | exact resolve b0e77 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1122 : x = (M.op (M.op (M.op y y) (M.op y y)) y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (k y x) := by
        first
        | (have i₁ := b0e77 y x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e77
        | (have j0 := b0e77 y x
           grind)
        | exact resolve b0e77 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1157 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op (M.op (M.op X1 X0) (M.op X1 X1)) X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 X1 X0
           have i₂ := b0e77 X1 X0
           grind)
        | (have i₁ := b0e14 X1 X1
           have i₂ := b0e77 X0 X1
           grind)
        | exact superpose b0e77 b0e14
        | (have j0 := b0e14 X0 X0
           have j1 := b0e77 X1 X0
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e77 X0 X1
           grind)
        | (have r₁ := b0e14 X0 X0
           have r₂ := b0e77 X0 X0
           grind)
        | exact resolve b0e14 b0e77
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e77
      have b0e1199 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X1)) X1) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e1157 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1157
      have b0e1202 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
        first
        | (have i₁ := b0e1122
           have i₂ := b0e11 y y
           grind)
        | exact superpose b0e11 b0e1122
        | exact resolve b0e1122 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1122
      have b0e1206 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b0e1118
           have i₂ := b0e11 (σ y) (σ y)
           grind)
        | exact superpose b0e11 b0e1118
        | exact resolve b0e1118 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1118
      have b0e1214 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b0e1206
           have i₂ := b0e47
           grind)
        | exact superpose b0e47 b0e1206
        | exact resolve b0e1206 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1206
      have b0e1220 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e1214
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e1214
        | exact resolve b0e1214 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1214
      have b0e7879 : (σ x) = (M.op (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b0e1199 (σ x) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e1199
        | (have j0 := b0e1199 (σ x) (σ y)
           grind)
        | exact resolve b0e1199 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e7885 : x = (M.op (M.op (M.op y y) (M.op y y)) y) ∨ (M.op y y) = (k y x) ∨ (M.op x y) = (k y x) := by
        first
        | (have i₁ := b0e1199 x y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e1199
        | (have j0 := b0e1199 x y
           grind)
        | exact resolve b0e1199 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1199
      have b0e8015 : (M.op x y) = (k y x) ∨ (M.op y y) = (k y x) ∨ x = y := by
        first
        | (have i₁ := b0e7885
           have i₂ := b0e11 y y
           grind)
        | exact superpose b0e11 b0e7885
        | exact resolve b0e7885 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7885
      have b0e8021 : (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b0e7879
           have i₂ := b0e11 (σ y) (σ y)
           grind)
        | exact superpose b0e11 b0e7879
        | exact resolve b0e7879 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7879
      have b0e8041 : (M.op (σ y) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b0e8021
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e8021
        | exact resolve b0e8021 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8021
      have b0e8053 : (σ (M.op y y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b0e8041
           have i₂ := b0e54 y
           grind)
        | exact superpose b0e54 b0e8041
        | exact resolve b0e8041 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8041
      have b0e8064 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op y y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e8053
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e8053
        | exact resolve b0e8053 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8053
      have b0e8081 : (M.op x y) ≠ (M.op y y) ∨ (M.op y y) = (k y x) ∨ x = y := by grind
      have b0e8099 : (M.op (σ y) (σ y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ x)) = (σ (k y x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e15 (σ y) (σ x)
           have i₂ := b0e1220
           grind)
        | exact superpose b0e1220 b0e15
        | (have j0 := b0e15 (σ y) (σ x)
           grind)
        | exact resolve b0e15 b0e1220
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e8125 : (σ (M.op x x)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
      clear b0e1220
      have b0e8137 : (σ (M.op y y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ x)) = (σ (k y x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e8099
           have i₂ := b0e54 y
           grind)
        | exact superpose b0e54 b0e8099
        | exact resolve b0e8099 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8099
      have b0e8156 : (σ (M.op x x)) = (σ (k y x)) ∨ (σ (M.op y y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e8137
           have i₂ := b0e47
           grind)
        | exact superpose b0e47 b0e8137
        | exact resolve b0e8137 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8137
      have b0e8169 : (σ (M.op y y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
        first
        | (have r₁ := b0e8156
           have r₂ := b0e8125
           grind)
        | exact resolve b0e8156 b0e8125
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8156
      have b0e8174 : (M.op (σ x) (σ x)) = (σ (k y x)) ∨ (σ (M.op y y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e8169
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e8169
        | exact resolve b0e8169 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8169
      have b0e8177 : (σ (M.op x x)) = (σ (k y x)) ∨ (σ (M.op y y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e8174
           have i₂ := b0e47
           grind)
        | exact superpose b0e47 b0e8174
        | exact resolve b0e8174 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47 b0e8174
      have b0e8178 : (σ (M.op y y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
        first
        | (have r₁ := b0e8177
           have r₂ := b0e8125
           grind)
        | exact resolve b0e8177 b0e8125
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8125 b0e8177
      have b0e39961 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op y y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e8064
           grind)
        | exact superpose b0e8064 b0e18
        | exact resolve b0e18 b0e8064
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8064
      have b0e40635 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op y y) = (k y x) ∨ x = y := by
        first
        | (have i₁ := b0e39961
           have i₂ := b0e8015
           grind)
        | exact superpose b0e8015 b0e39961
        | exact resolve b0e39961 b0e8015
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8015
      have b0e40636 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
        first
        | (have i₁ := b0e39961
           have i₂ := b0e1202
           grind)
        | exact superpose b0e1202 b0e39961
        | exact resolve b0e39961 b0e1202
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1202 b0e39961
      have b0e40659 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
      clear b0e40636
      have b0e40660 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op y y) = (k y x) ∨ x = y := by grind
      clear b0e40635
      have b0e43363 : (M.op x y) = (τ (σ (M.op y y))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
        first
        | (have i₁ := b0e12 (M.op x y)
           have i₂ := b0e40659
           grind)
        | exact superpose b0e40659 b0e12
        | exact resolve b0e12 b0e40659
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40659
      have b0e43433 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
        first
        | (have i₁ := b0e43363
           have i₂ := b0e12 (M.op y y)
           grind)
        | exact superpose b0e12 b0e43363
        | exact resolve b0e43363 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43363
      have b0e44622 : (M.op x y) = (τ (σ (M.op y y))) ∨ (σ x) = (σ y) ∨ (M.op y y) = (k y x) ∨ x = y := by
        first
        | (have i₁ := b0e12 (M.op x y)
           have i₂ := b0e40660
           grind)
        | exact superpose b0e40660 b0e12
        | exact resolve b0e12 b0e40660
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40660
      have b0e44692 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op y y) = (k y x) ∨ x = y := by
        first
        | (have i₁ := b0e44622
           have i₂ := b0e12 (M.op y y)
           grind)
        | exact superpose b0e12 b0e44622
        | exact resolve b0e44622 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44622
      have b0e44693 : (M.op y y) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
        first
        | (have r₁ := b0e44692
           have r₂ := b0e8081
           grind)
        | exact resolve b0e44692 b0e8081
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8081 b0e44692
      have b0e44722 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
        first
        | (have i₁ := b0e8178
           have i₂ := b0e44693
           grind)
        | exact superpose b0e44693 b0e8178
        | exact resolve b0e8178 b0e44693
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8178 b0e44693
      have b0e44759 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
      clear b0e44722
      have b0e44760 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
      clear b0e44759
      have b0e45475 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e44760
           grind)
        | exact superpose b0e44760 b0e18
        | exact resolve b0e18 b0e44760
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44760
      have b0e45759 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
        first
        | (have i₁ := b0e45475
           have i₂ := b0e43433
           grind)
        | exact superpose b0e43433 b0e45475
        | exact resolve b0e45475 b0e43433
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43433 b0e45475
      have b0e45761 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by grind
      clear b0e45759
      have b0e45762 : (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
      clear b0e45761
      have b0e45901 : x = (M.op (M.op (M.op y y) (M.op y y)) y) ∨ x = y ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e23
           have i₂ := b0e45762
           grind)
        | exact superpose b0e45762 b0e23
        | exact resolve b0e23 b0e45762
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23 b0e45762
      have b0e45961 : x = y ∨ x = y ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e45901
           have i₂ := b0e11 y y
           grind)
        | exact superpose b0e11 b0e45901
        | exact resolve b0e45901 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45901
      have b0e45962 : (σ x) = (σ y) ∨ x = y := by grind
      clear b0e45961
      have b0e46132 : x = (τ (σ y)) ∨ x = y := by
        first
        | (have i₁ := b0e12 x
           have i₂ := b0e45962
           grind)
        | exact superpose b0e45962 b0e12
        | exact resolve b0e12 b0e45962
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45962
      have b0e46199 : x = y ∨ x = y := by
        first
        | (have i₁ := b0e46132
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e46132
        | exact resolve b0e46132 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46132
      have b0e46200 : x = y := by grind
      clear b0e46199
      have b0e46772 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e46200
           grind)
        | exact superpose b0e46200 b0e18
        | exact resolve b0e18 b0e46200
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46200
      have b0e46823 : False := by grind
      exact b0e46823
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : (M.op y x) = (M.op y y) := by grind
        have b1e21 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e51 : (M.op y y) ≠ (M.op y y) ∨ (k x y) = (M.op x x) := by
          first
          | (have i₁ := b1e15 x y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e15
          | (have j0 := b1e15 y y
             grind)
          | (have r₁ := b1e15 x y
             have r₂ := b1e20
             grind)
          | exact resolve b1e15 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e52 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b1e15 (σ x) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e55 : (M.op (σ y) (σ x)) = (k (σ x) (σ x)) := by grind
        clear b1e52
        have b1e56 : (k x y) = (M.op x x) := by grind
        clear b1e51
        have b1e57 : (M.op (σ y) (σ x)) = (σ (k x x)) := by
          first
          | (have i₁ := b1e55
             have i₂ := b1e18 x x
             grind)
          | exact superpose b1e18 b1e55
          | exact resolve b1e55 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55
        have b1e58 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e57
             have i₂ := b1e54 x
             grind)
          | exact superpose b1e54 b1e57
          | exact resolve b1e57 b1e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57
        have b1e60 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e54 (σ X0)
             grind)
          | exact superpose b1e54 b1e18
          | exact resolve b1e18 b1e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e60 X0
             have i₂ := b1e54 X0
             grind)
          | exact superpose b1e54 b1e60
          | exact resolve b1e60 b1e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54 b1e60
        have b1e74 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 X0) = (M.op X0 (σ x)) ∨ (M.op X0 X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e16 (σ x) X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e16
          | (have j0 := b1e16 (σ x) X0
             grind)
          | (have r₁ := b1e16 (σ x) (σ y)
             have r₂ := b1e22
             grind)
          | exact resolve b1e16 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e76 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 X0) = (M.op X0 (σ x)) ∨ (M.op X0 X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e74 X0
             have i₂ := b1e58
             grind)
          | exact superpose b1e58 b1e74
          | (have j0 := b1e74 X0
             grind)
          | exact resolve b1e74 b1e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e74
        have b1e131 : (M.op (σ y) (σ y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e58
             grind)
          | exact superpose b1e58 b1e21
          | exact resolve b1e21 b1e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e136 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e131
             have i₂ := b1e67 y
             grind)
          | exact superpose b1e67 b1e131
          | exact resolve b1e131 b1e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e131
        have b1e764 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e76 (σ y)
             have i₂ := b1e58
             grind)
          | exact superpose b1e58 b1e76
          | (have j0 := b1e76 (σ y)
             grind)
          | (have r₁ := b1e76 (σ y)
             have r₂ := b1e58
             grind)
          | exact resolve b1e76 b1e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e58 b1e76
        have b1e767 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b1e764
        have b1e770 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e767
             have i₂ := b1e67 y
             grind)
          | exact superpose b1e67 b1e767
          | exact resolve b1e767 b1e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e767
        have b1e774 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e770
             have r₂ := b1e136
             grind)
          | exact resolve b1e770 b1e136
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e770
        have b1e778 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e774
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e774
          | exact resolve b1e774 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e774
        have b1e780 : (M.op (σ y) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e778
             have i₂ := b1e56
             grind)
          | exact superpose b1e56 b1e778
          | exact resolve b1e778 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56 b1e778
        have b1e782 : (σ (M.op x x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e780
             have i₂ := b1e67 y
             grind)
          | exact superpose b1e67 b1e780
          | exact resolve b1e780 b1e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e67 b1e780
        have b1e784 : False := by grind
        exact b1e784
      · have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op y x) = (M.op y y) := by grind
        have b2e21 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (M.op (σ y) (σ x)) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e49 : (M.op y y) ≠ (M.op y y) ∨ (k x y) = (M.op x x) := by
          first
          | (have i₁ := b2e15 x y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e15
          | (have j0 := b2e15 y y
             grind)
          | (have r₁ := b2e15 x y
             have r₂ := b2e20
             grind)
          | exact resolve b2e15 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e50 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e51 : (k x y) = (M.op x x) := by grind
        clear b2e49
        have b2e53 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e50 (σ X0)
             grind)
          | exact superpose b2e50 b2e18
          | exact resolve b2e18 b2e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e60 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e53 X0
             have i₂ := b2e50 X0
             grind)
          | exact superpose b2e50 b2e53
          | exact resolve b2e53 b2e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50 b2e53
        have b2e94 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 X0) = (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e22
             have i₂ := b2e17 (σ x) X0
             grind)
          | (have i₁ := b2e22
             have i₂ := b2e17 (σ x) (σ x)
             grind)
          | exact superpose b2e17 b2e22
          | (have j1 := b2e17 (σ x) X0
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | exact resolve b2e22 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e142 : (M.op (σ y) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e60 x
             grind)
          | exact superpose b2e60 b2e22
          | exact resolve b2e22 b2e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e60
        have b2e1401 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e94 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e94
        have b2e1402 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1401
             have r₂ := b2e21
             grind)
          | exact resolve b2e1401 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1401
        have b2e1408 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1402
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1402
          | exact resolve b2e1402 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1402
        have b2e1412 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e1408
             have i₂ := b2e51
             grind)
          | exact superpose b2e51 b2e1408
          | exact resolve b2e1408 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51 b2e1408
        have b2e1413 : False := by grind
        exact b2e1413
  · rcases eq_or_ne (M.op x x) (M.op y x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : (M.op y x) ≠ (M.op y y) := by grind
        have b3e21 : (M.op y x) = (M.op x x) := by grind
        have b3e22 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e52 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e15 (σ x) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e15
          | (have j0 := b3e15 (σ y) (σ y)
             grind)
          | (have r₁ := b3e15 (σ x) (σ y)
             have r₂ := b3e22
             grind)
          | exact resolve b3e15 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e55 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear b3e52
        have b3e57 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e55
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e55
          | exact resolve b3e55 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e55
        have b3e74 : ∀ X0 : G, (M.op y x) ≠ (M.op X0 x) ∨ (M.op X0 X0) = (M.op X0 x) ∨ (M.op X0 X0) = (k x X0) := by
          intro X0
          first
          | (have i₁ := b3e16 x X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e16
          | (have j0 := b3e16 x X0
             grind)
          | (have r₁ := b3e16 x y
             have r₂ := b3e21
             grind)
          | exact resolve b3e16 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e78 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b3e15 (σ x) (σ x)
             have i₂ := b3e57
             grind)
          | exact superpose b3e57 b3e15
          | exact resolve b3e15 b3e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e57
        have b3e81 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
        clear b3e78
        have b3e84 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b3e81
             have i₂ := b3e18 x x
             grind)
          | exact superpose b3e18 b3e81
          | exact resolve b3e81 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e81
        have b3e85 : (σ (k x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e84
             have i₂ := b3e54 x
             grind)
          | exact superpose b3e54 b3e84
          | exact resolve b3e84 b3e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54 b3e84
        have b3e86 : (σ (k x y)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b3e85
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e85
          | exact resolve b3e85 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e85
        have b3e140 : (k x y) = (τ (σ (M.op y x))) := by
          first
          | (have i₁ := b3e13 (k x y)
             have i₂ := b3e86
             grind)
          | exact superpose b3e86 b3e13
          | exact resolve b3e13 b3e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e86
        have b3e141 : (M.op y x) = (k x y) := by
          first
          | (have i₁ := b3e140
             have i₂ := b3e13 (M.op y x)
             grind)
          | exact superpose b3e13 b3e140
          | exact resolve b3e140 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e140
        have b3e376 : (M.op y x) = (M.op y y) ∨ (M.op y y) = (k x y) := by
          first
          | (have j0 := b3e74 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e74
        have b3e377 : (M.op y y) = (k x y) := by
          first
          | (have r₁ := b3e376
             have r₂ := b3e20
             grind)
          | exact resolve b3e376 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e376
        have b3e380 : (M.op y x) = (M.op y y) := by
          first
          | (have i₁ := b3e141
             have i₂ := b3e377
             grind)
          | exact superpose b3e377 b3e141
          | exact resolve b3e141 b3e377
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e141 b3e377
        have b3e385 : False := by grind
        exact b3e385
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) (M.op X0 X1)) X1) = X0 := by
            intro X0 X1
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : (M.op y x) ≠ (M.op y y) := by grind
          have b4e22 : (M.op y x) = (M.op x x) := by grind
          have b4e23 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          have b4e24 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e25 : (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e23
            | exact resolve b4e23 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e26 : (M.op y y) ≠ (M.op x x) := by
            first
            | (have i₁ := b4e21
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e21
            | exact resolve b4e21 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 (τ X0) X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e19
            | exact resolve b4e19 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e28 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b4e32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k (τ X0) X1)
               have i₂ := b4e27 X0 X1
               grind)
            | exact superpose b4e27 b4e14
            | exact resolve b4e14 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e42 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k X0 (τ X1))
               have i₂ := b4e28 X1 X0
               grind)
            | exact superpose b4e28 b4e14
            | exact resolve b4e14 b4e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e32 X1 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e32
            | exact resolve b4e32 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e69 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e67 (σ X0)
               grind)
            | exact superpose b4e67 b4e19
            | exact resolve b4e19 b4e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e72 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
            intro X0
            first
            | (have i₁ := b4e28 X0 (τ X0)
               have i₂ := b4e67 (τ X0)
               grind)
            | exact superpose b4e67 b4e28
            | exact resolve b4e28 b4e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e75 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e72 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e72
            | exact resolve b4e72 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e72
          have b4e78 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e69 X0
               have i₂ := b4e67 X0
               grind)
            | exact superpose b4e67 b4e69
            | exact resolve b4e69 b4e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e69
          have b4e81 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e75 X0
               have i₂ := b4e67 X0
               grind)
            | exact superpose b4e67 b4e75
            | exact resolve b4e75 b4e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e67 b4e75
          have b4e102 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X1 X0
               have i₂ := b4e18 X1 X0
               grind)
            | (have i₁ := b4e16 X1 X1
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e16
            | (have j0 := b4e16 X0 X0
               have j1 := b4e18 X1 X0
               grind)
            | (have r₁ := b4e16 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e16 X0 X0
               have r₂ := b4e18 X0 X0
               grind)
            | (have r₁ := b4e16 X1 X1
               have r₂ := b4e18 X1 X1
               grind)
            | exact resolve b4e16 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e104 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X0)) X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 X0
               have i₂ := b4e18 X1 X0
               grind)
            | (have i₁ := b4e13 X1 X1
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e13
            | (have j1 := b4e18 X1 X0
               grind)
            | exact resolve b4e13 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e112 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 X0 X1
               have i₂ := b4e18 X0 X1
               grind)
            | (have i₁ := b4e17 X0 X0
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e17
            | (have j0 := b4e17 X0 X1
               have j1 := b4e18 X0 X1
               grind)
            | (have r₁ := b4e17 X1 X1
               have r₂ := b4e18 X1 X1
               grind)
            | (have r₁ := b4e17 X0 X0
               have r₂ := b4e18 X0 X0
               grind)
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | exact resolve b4e17 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e125 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 X0
               have i₂ := b4e18 (σ X1) (σ X0)
               grind)
            | exact superpose b4e18 b4e19
            | (have j1 := b4e18 (σ X1) (σ X0)
               grind)
            | exact resolve b4e19 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e130 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e18 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e133 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e112 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e112
          have b4e135 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e102 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e102
          have b4e138 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e125 X0 X1
               have i₂ := b4e78 X0
               grind)
            | exact superpose b4e78 b4e125
            | (have j0 := b4e125 X0 X1
               grind)
            | exact resolve b4e125 b4e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e125
          have b4e142 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e133 X0 X1
               have j1 := b4e130 X1 X0
               grind)
            | (have r₁ := b4e133 X0 X1
               have r₂ := b4e130 X0 X1
               grind)
            | (have r₁ := b4e133 X1 X0
               have r₂ := b4e130 X0 X1
               grind)
            | (have r₁ := b4e133 X0 X0
               have r₂ := b4e130 X0 X0
               grind)
            | exact resolve b4e133 b4e130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e130 b4e133
          have b4e146 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e138 X0 X1
               have i₂ := b4e78 X1
               grind)
            | exact superpose b4e78 b4e138
            | (have j0 := b4e138 X0 X1
               grind)
            | exact resolve b4e138 b4e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e138
          have b4e153 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b4e25
               have i₂ := b4e78 y
               grind)
            | exact superpose b4e78 b4e25
            | exact resolve b4e25 b4e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e159 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 (σ X0) X1
               have i₂ := b4e78 X0
               grind)
            | exact superpose b4e78 b4e17
            | (have j0 := b4e17 (σ X0) X1
               grind)
            | exact resolve b4e17 b4e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e160 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X1 (σ X0)
               have i₂ := b4e78 X0
               grind)
            | exact superpose b4e78 b4e16
            | (have j0 := b4e16 X1 (σ X0)
               grind)
            | exact resolve b4e16 b4e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e165 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e153
               have i₂ := b4e78 x
               grind)
            | exact superpose b4e78 b4e153
            | exact resolve b4e153 b4e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e153
          have b4e182 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e14 (M.op (τ X0) (τ X0))
               have i₂ := b4e81 X0
               grind)
            | exact superpose b4e81 b4e14
            | exact resolve b4e14 b4e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e242 : ∀ X0 X1 : G, (M.op (τ X0) X1) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X1 (τ X0)
               have i₂ := b4e182 X0
               grind)
            | exact superpose b4e182 b4e16
            | (have j0 := b4e16 X1 (τ X0)
               grind)
            | exact resolve b4e16 b4e182
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e519 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 X0)) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (M.op X0 X0) = (M.op (τ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e28 X1 X0
               have i₂ := b4e135 (τ X1) X0
               grind)
            | exact superpose b4e135 b4e28
            | (have j1 := b4e135 (τ X1) X0
               grind)
            | exact resolve b4e28 b4e135
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e135
          have b4e702 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e28 X0 X1
               have i₂ := b4e142 X1 (τ X0)
               grind)
            | exact superpose b4e142 b4e28
            | (have j1 := b4e142 X1 (τ X0)
               grind)
            | exact resolve b4e28 b4e142
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28
          have b4e720 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e27 X1 X0
               have i₂ := b4e142 (τ X1) X0
               grind)
            | exact superpose b4e142 b4e27
            | (have j1 := b4e142 (τ X1) X0
               grind)
            | exact resolve b4e27 b4e142
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e142
          have b4e746 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e702 X0 X1
               have i₂ := b4e81 X0
               grind)
            | exact superpose b4e81 b4e702
            | (have j0 := b4e702 X0 X1
               grind)
            | exact resolve b4e702 b4e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e702
          have b4e775 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e746 X0 X1
               have i₂ := b4e182 X0
               grind)
            | exact superpose b4e182 b4e746
            | (have j0 := b4e746 X0 X1
               grind)
            | exact resolve b4e746 b4e182
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e746
          have b4e989 : (σ y) = (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b4e104 (σ x) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e104
            | (have j0 := b4e104 (σ x) (σ y)
               grind)
            | exact resolve b4e104 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e992 : y = (M.op (M.op (M.op x x) (M.op x x)) x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b4e104 x y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e104
            | (have j0 := b4e104 x y
               grind)
            | exact resolve b4e104 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1015 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op (M.op (M.op X1 X1) (M.op X0 X1)) X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 X1 X0
               have i₂ := b4e104 X0 X1
               grind)
            | (have i₁ := b4e17 X1 X1
               have i₂ := b4e104 X0 X1
               grind)
            | exact superpose b4e104 b4e17
            | (have j0 := b4e17 X0 X0
               have j1 := b4e104 X1 X0
               grind)
            | (have r₁ := b4e17 X0 (M.op (M.op X0 X0) (M.op (M.op X0 X0) X0))
               have r₂ := b4e104 X0 (M.op X0 X0)
               grind)
            | (have r₁ := b4e17 X1 X0
               have r₂ := b4e104 X0 X1
               grind)
            | (have r₁ := b4e17 X0 X0
               have r₂ := b4e104 X0 X0
               grind)
            | exact resolve b4e17 b4e104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e104
          have b4e1050 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) (M.op X0 X1)) X1) = X0 ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e1015 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1015
          have b4e1053 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b4e992
               have i₂ := b4e13 x x
               grind)
            | exact superpose b4e13 b4e992
            | exact resolve b4e992 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e992
          have b4e1056 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b4e989
               have i₂ := b4e13 (σ x) (σ x)
               grind)
            | exact superpose b4e13 b4e989
            | exact resolve b4e989 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e989
          have b4e1063 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b4e1056
               have i₂ := b4e78 y
               grind)
            | exact superpose b4e78 b4e1056
            | exact resolve b4e1056 b4e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1056
          have b4e1068 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e1063
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e1063
            | exact resolve b4e1063 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1063
          have b4e2703 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e160 X1 (σ X0)
               have i₂ := b4e146 X1 X0
               grind)
            | exact superpose b4e146 b4e160
            | (have j0 := b4e160 X1 (σ X0)
               have j1 := b4e146 X1 X0
               grind)
            | (have r₁ := b4e160 X0 (σ X0)
               have r₂ := b4e146 X0 X0
               grind)
            | (have r₁ := b4e160 X0 (σ X1)
               have r₂ := b4e146 X0 X1
               grind)
            | exact resolve b4e160 b4e146
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2759 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e146 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2760 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e146 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e146
          have b4e2828 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e2703 X0 X1
               have j1 := b4e160 X1 (σ X0)
               grind)
            | (have r₁ := b4e2703 X0 X0
               have r₂ := b4e160 X0 (σ X0)
               grind)
            | (have r₁ := b4e2703 X0 X0
               have r₂ := b4e160 X0 (σ X0)
               grind)
            | exact resolve b4e2703 b4e160
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e160 b4e2703
          have b4e2912 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e2828 X0 X1
               have i₂ := b4e78 X0
               grind)
            | exact superpose b4e78 b4e2828
            | (have j0 := b4e2828 X0 X1
               grind)
            | exact resolve b4e2828 b4e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2828
          have b4e2968 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e2912 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e2912
            | (have j0 := b4e2912 X0 X1
               grind)
            | exact resolve b4e2912 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2912
          have b4e8634 : (σ (M.op y y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by grind
          have b4e10380 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (k X0 (τ (σ X1))) = (M.op (τ (σ X1)) X0) ∨ (M.op X0 X0) = (M.op (τ (σ X1)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X0 X1
               have i₂ := b4e519 X0 (σ X1)
               grind)
            | exact superpose b4e519 b4e19
            | (have j1 := b4e519 X0 (σ X1)
               grind)
            | exact resolve b4e19 b4e519
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e519
          have b4e10503 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (τ (σ X1)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e10380 X0 X0
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e10380
            | (have j0 := b4e10380 X0 X1
               grind)
            | exact resolve b4e10380 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10380
          have b4e10555 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e10503 X0 X1
               have i₂ := b4e14 X1
               grind)
            | exact superpose b4e14 b4e10503
            | (have j0 := b4e10503 X0 X1
               grind)
            | exact resolve b4e10503 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10503
          have b4e13312 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e720 X0 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e720
            | exact resolve b4e720 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e720
          have b4e13648 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13312 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e13312
            | (have j0 := b4e13312 X0 X1
               grind)
            | exact resolve b4e13312 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13312
          have b4e14264 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e242 X0 X1
               have i₂ := b4e775 X0 X1
               grind)
            | exact superpose b4e775 b4e242
            | (have j0 := b4e242 X0 X1
               have j1 := b4e775 X0 X1
               grind)
            | (have r₁ := b4e242 X0 X1
               have r₂ := b4e775 X0 X1
               grind)
            | exact resolve b4e242 b4e775
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e775
          have b4e14534 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have j0 := b4e14264 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e14264
          have b4e30021 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e2759 (τ X1) (τ X0)
               have i₂ := b4e47 X1 X0
               grind)
            | exact superpose b4e47 b4e2759
            | (have j0 := b4e2759 (τ X1) (τ X0)
               grind)
            | exact resolve b4e2759 b4e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2759
          have b4e30147 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e30021 X0 X1
               have i₂ := b4e15 (k X0 X1)
               grind)
            | exact superpose b4e15 b4e30021
            | (have j0 := b4e30021 X0 X1
               grind)
            | exact resolve b4e30021 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30021
          have b4e30193 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e30147 X0 X1
               have i₂ := b4e81 X0
               grind)
            | exact superpose b4e81 b4e30147
            | (have j0 := b4e30147 X0 X1
               grind)
            | exact resolve b4e30147 b4e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30147
          have b4e30230 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e30193 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e30193
            | (have j0 := b4e30193 X0 X1
               grind)
            | exact resolve b4e30193 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30193
          have b4e30260 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e30230 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e30230
            | (have j0 := b4e30230 X0 X1
               grind)
            | exact resolve b4e30230 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30230
          have b4e30285 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e30260 X0 X1
               have i₂ := b4e81 X0
               grind)
            | exact superpose b4e81 b4e30260
            | (have j0 := b4e30260 X0 X1
               grind)
            | exact resolve b4e30260 b4e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30260
          have b4e30306 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e30285 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e30285
            | (have j0 := b4e30285 X0 X1
               grind)
            | exact resolve b4e30285 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30285
          have b4e30323 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e30306 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e30306
            | (have j0 := b4e30306 X0 X1
               grind)
            | exact resolve b4e30306 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30306
          have b4e30336 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e30323 X0 X1
               have i₂ := b4e81 X1
               grind)
            | exact superpose b4e81 b4e30323
            | (have j0 := b4e30323 X0 X1
               grind)
            | exact resolve b4e30323 b4e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30323
          have b4e30524 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e2760 (τ X1) (τ X0)
               have i₂ := b4e47 X1 X0
               grind)
            | exact superpose b4e47 b4e2760
            | (have j0 := b4e2760 (τ X1) (τ X0)
               grind)
            | exact resolve b4e2760 b4e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e30652 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e30524 X0 X1
               have i₂ := b4e15 (k X0 X1)
               grind)
            | exact superpose b4e15 b4e30524
            | (have j0 := b4e30524 X0 X1
               grind)
            | exact resolve b4e30524 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30524
          have b4e30699 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e30652 X0 X1
               have i₂ := b4e81 X1
               grind)
            | exact superpose b4e81 b4e30652
            | (have j0 := b4e30652 X0 X1
               grind)
            | exact resolve b4e30652 b4e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30652
          have b4e30734 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e30699 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e30699
            | (have j0 := b4e30699 X0 X1
               grind)
            | exact resolve b4e30699 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30699
          have b4e30761 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e30734 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e30734
            | (have j0 := b4e30734 X0 X1
               grind)
            | exact resolve b4e30734 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30734
          have b4e30784 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e30761 X0 X1
               have i₂ := b4e81 X0
               grind)
            | exact superpose b4e81 b4e30761
            | (have j0 := b4e30761 X0 X1
               grind)
            | exact resolve b4e30761 b4e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30761
          have b4e30806 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e30784 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e30784
            | (have j0 := b4e30784 X0 X1
               grind)
            | exact resolve b4e30784 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30784
          have b4e30823 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e30806 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e30806
            | (have j0 := b4e30806 X0 X1
               grind)
            | exact resolve b4e30806 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30806
          have b4e30836 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e30823 X0 X1
               have i₂ := b4e81 X1
               grind)
            | exact superpose b4e81 b4e30823
            | (have j0 := b4e30823 X0 X1
               grind)
            | exact resolve b4e30823 b4e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30823
          have b4e37185 : (σ y) = (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b4e1050 (σ y) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e1050
            | (have j0 := b4e1050 (σ y) (σ x)
               grind)
            | exact resolve b4e1050 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e37193 : y = (M.op (M.op (M.op x x) (M.op x x)) x) ∨ (M.op y y) = (M.op x x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b4e1050 y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e1050
            | (have j0 := b4e1050 y x
               grind)
            | exact resolve b4e1050 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1050
          have b4e37928 : y = (M.op (M.op (M.op x x) (M.op x x)) x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (k y x) := by
            first
            | (have r₁ := b4e37193
               have r₂ := b4e26
               grind)
            | exact resolve b4e37193 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37193
          have b4e37936 : (σ y) = (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b4e37185
               have r₂ := b4e25
               grind)
            | exact resolve b4e37185 b4e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37185
          have b4e38010 : (M.op x y) = (k y x) ∨ (M.op x x) = (k y x) ∨ x = y := by
            first
            | (have i₁ := b4e37928
               have i₂ := b4e13 x x
               grind)
            | exact superpose b4e13 b4e37928
            | exact resolve b4e37928 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37928
          have b4e38017 : (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b4e37936
               have i₂ := b4e13 (σ x) (σ x)
               grind)
            | exact superpose b4e13 b4e37936
            | exact resolve b4e37936 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37936
          have b4e38072 : (M.op (σ x) (σ x)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b4e38017
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e38017
            | exact resolve b4e38017 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38017
          have b4e38107 : (σ (M.op x x)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b4e38072
               have i₂ := b4e78 x
               grind)
            | exact superpose b4e78 b4e38072
            | exact resolve b4e38072 b4e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38072
          have b4e38131 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x x)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e38107
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e38107
            | exact resolve b4e38107 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38107
          have b4e38258 : (M.op x y) ≠ (M.op x x) ∨ (M.op x x) = (k y x) ∨ x = y := by grind
          clear b4e38010
          have b4e39422 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e38131
               grind)
            | exact superpose b4e38131 b4e20
            | exact resolve b4e20 b4e38131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39434 : (σ (M.op y y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ x)) = (σ (k y x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ (M.op x x)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e159 y (σ x)
               have i₂ := b4e38131
               grind)
            | exact superpose b4e38131 b4e159
            | (have j0 := b4e159 y (σ x)
               grind)
            | exact resolve b4e159 b4e38131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e159 b4e38131
          have b4e39506 : (σ (M.op x x)) = (σ (k y x)) ∨ (σ (M.op y y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ (M.op x x)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e39434
               have i₂ := b4e78 x
               grind)
            | exact superpose b4e78 b4e39434
            | exact resolve b4e39434 b4e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39434
          have b4e39507 : (σ (M.op x x)) = (σ (k y x)) ∨ (σ (M.op y y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
          clear b4e39506
          have b4e39535 : (M.op (σ x) (σ x)) = (σ (k y x)) ∨ (σ (M.op x x)) = (σ (k y x)) ∨ (σ (M.op y y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e39507
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e39507
            | exact resolve b4e39507 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39507
          have b4e39549 : (σ (M.op x x)) = (σ (k y x)) ∨ (σ (M.op x x)) = (σ (k y x)) ∨ (σ (M.op y y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e39535
               have i₂ := b4e78 x
               grind)
            | exact superpose b4e78 b4e39535
            | exact resolve b4e39535 b4e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39535
          have b4e39550 : (σ (M.op y y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (k y x)) ∨ (σ x) = (σ y) := by grind
          clear b4e39549
          have b4e40957 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b4e39550
               have i₂ := b4e10555 y x
               grind)
            | exact superpose b4e10555 b4e39550
            | (have j1 := b4e10555 y x
               grind)
            | (have r₁ := b4e39550
               have r₂ := b4e10555 y x
               grind)
            | exact resolve b4e39550 b4e10555
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10555
          have b4e40958 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b4e40957
          have b4e40960 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b4e40958
               have r₂ := b4e165
               grind)
            | exact resolve b4e40958 b4e165
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40958
          have b4e41655 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b4e39422
               have i₂ := b4e40960
               grind)
            | exact superpose b4e40960 b4e39422
            | exact resolve b4e39422 b4e40960
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41666 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
          clear b4e41655
          have b4e41667 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
          clear b4e41666
          have b4e42216 : (M.op x y) = (τ (σ (M.op x x))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b4e14 (M.op x y)
               have i₂ := b4e41667
               grind)
            | exact superpose b4e41667 b4e14
            | exact resolve b4e14 b4e41667
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41667
          have b4e42289 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b4e42216
               have i₂ := b4e14 (M.op x x)
               grind)
            | exact superpose b4e14 b4e42216
            | exact resolve b4e42216 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42216
          have b4e42834 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b4e165
               have i₂ := b4e42289
               grind)
            | exact superpose b4e42289 b4e165
            | exact resolve b4e165 b4e42289
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42289
          have b4e77573 : ∀ X0 X1 : G, (k X0 (σ (τ X1))) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e27 X0 (τ X1)
               have i₂ := b4e14534 X1 (τ X0)
               grind)
            | exact superpose b4e14534 b4e27
            | (have j1 := b4e14534 X1 (τ X0)
               grind)
            | exact resolve b4e27 b4e14534
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27
          have b4e77964 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e32 (σ X1) X0
               have i₂ := b4e14534 (σ X0) X1
               grind)
            | exact superpose b4e14534 b4e32
            | (have j1 := b4e14534 (σ X0) X1
               grind)
            | exact resolve b4e32 b4e14534
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e14534
          have b4e78180 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e77964 X0 X1
               have i₂ := b4e14 X1
               grind)
            | exact superpose b4e14 b4e77964
            | (have j0 := b4e77964 X0 X1
               grind)
            | exact resolve b4e77964 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e77964
          have b4e78341 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ (τ X1))) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e77573 X0 X1
               have i₂ := b4e81 X0
               grind)
            | exact superpose b4e81 b4e77573
            | (have j0 := b4e77573 X0 X1
               grind)
            | exact resolve b4e77573 b4e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e81 b4e77573
          have b4e78583 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e78180 X0 X1
               have i₂ := b4e78 X0
               grind)
            | exact superpose b4e78 b4e78180
            | (have j0 := b4e78180 X0 X1
               grind)
            | exact resolve b4e78180 b4e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78180
          have b4e78662 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e78341 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e78341
            | (have j0 := b4e78341 X0 X1
               grind)
            | exact resolve b4e78341 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78341
          have b4e78800 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e78583 X0 X1
               have i₂ := b4e14 (M.op X0 X0)
               grind)
            | exact superpose b4e14 b4e78583
            | (have j0 := b4e78583 X0 X1
               grind)
            | exact resolve b4e78583 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78583
          have b4e78864 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e78662 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e78662
            | (have j0 := b4e78662 X0 X1
               grind)
            | exact resolve b4e78662 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78662
          have b4e78956 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e78800 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e78800
            | (have j0 := b4e78800 X0 X1
               grind)
            | exact resolve b4e78800 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78800
          have b4e79008 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e78864 X0 X1
               have i₂ := b4e47 X1 X0
               grind)
            | exact superpose b4e47 b4e78864
            | (have j0 := b4e78864 X0 X1
               grind)
            | exact resolve b4e78864 b4e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78864
          have b4e79055 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e78956 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e78956
            | (have j0 := b4e78956 X0 X1
               grind)
            | exact resolve b4e78956 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78956
          have b4e83687 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b4e39550
               have i₂ := b4e79055 x y
               grind)
            | exact superpose b4e79055 b4e39550
            | (have j1 := b4e79055 x y
               grind)
            | exact resolve b4e39550 b4e79055
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39550
          have b4e84013 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e32 X1 X0
               have i₂ := b4e79055 (σ X0) X1
               grind)
            | exact superpose b4e79055 b4e32
            | (have j1 := b4e79055 (σ X0) X1
               grind)
            | exact resolve b4e32 b4e79055
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e84195 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e79055 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e79055
          have b4e84246 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) ∨ (M.op x x) = (k y x) := by grind
          clear b4e83687
          have b4e84481 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e84013 X0 X1
               have i₂ := b4e78 X0
               grind)
            | exact superpose b4e78 b4e84013
            | (have j0 := b4e84013 X0 X1
               grind)
            | exact resolve b4e84013 b4e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e84013
          have b4e84554 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x x) = (k y x) := by
            first
            | (have r₁ := b4e84246
               have r₂ := b4e165
               grind)
            | exact resolve b4e84246 b4e165
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e84246
          have b4e85094 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e84481 X0 X1
               have i₂ := b4e14 (M.op X0 X0)
               grind)
            | exact superpose b4e14 b4e84481
            | (have j0 := b4e84481 X0 X1
               grind)
            | exact resolve b4e84481 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e84481
          have b4e85628 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b4e39422
               have i₂ := b4e84554
               grind)
            | exact superpose b4e84554 b4e39422
            | exact resolve b4e39422 b4e84554
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39422
          have b4e85639 : (M.op x y) ≠ (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x x) = (k y x) := by grind
          clear b4e84554
          have b4e85644 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (k y x) := by grind
          clear b4e85628
          have b4e85645 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (k y x) := by grind
          clear b4e85644
          have b4e92895 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b4e42834
               have i₂ := b4e85645
               grind)
            | exact superpose b4e85645 b4e42834
            | (have r₁ := b4e42834
               have r₂ := b4e85645
               grind)
            | exact resolve b4e42834 b4e85645
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42834 b4e85645
          have b4e93003 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) := by grind
          clear b4e92895
          have b4e93004 : (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) := by grind
          clear b4e93003
          have b4e93077 : (M.op x x) = (k y x) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b4e93004
               have r₂ := b4e85639
               grind)
            | exact resolve b4e93004 b4e85639
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e85639 b4e93004
          have b4e102768 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e79008 X0 X1
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e79008
            | (have j1 := b4e18 X1 X0
               grind)
            | exact resolve b4e79008 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e103804 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e30336 X0 X1
               have i₂ := b4e79008 X0 X1
               grind)
            | exact superpose b4e79008 b4e30336
            | (have j0 := b4e30336 X0 X1
               have j1 := b4e79008 X0 X1
               grind)
            | (have r₁ := b4e30336 X1 X1
               have r₂ := b4e79008 X1 X1
               grind)
            | (have r₁ := b4e30336 X0 X1
               have r₂ := b4e79008 X0 X1
               grind)
            | exact resolve b4e30336 b4e79008
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e104309 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e103804 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e103804
          have b4e104594 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e102768 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e102768
          have b4e104920 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e104309 X0 X1
               have j1 := b4e30836 X0 X1
               grind)
            | (have r₁ := b4e104309 X0 X1
               have r₂ := b4e30836 X0 X1
               grind)
            | exact resolve b4e104309 b4e30836
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e104309
          have b4e115302 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e104594 X1 X0
               have i₂ := b4e79008 X0 X1
               grind)
            | exact superpose b4e79008 b4e104594
            | (have j0 := b4e104594 X1 X0
               have j1 := b4e79008 X0 X1
               grind)
            | exact resolve b4e104594 b4e79008
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e115879 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e79008 X1 X0
               have i₂ := b4e104594 X0 X1
               grind)
            | exact superpose b4e104594 b4e79008
            | (have j0 := b4e79008 X1 X0
               have j1 := b4e104594 X0 X1
               grind)
            | exact resolve b4e79008 b4e104594
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e79008
          have b4e116010 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X1 X0
               have i₂ := b4e104594 X0 X1
               grind)
            | (have i₁ := b4e16 X0 X0
               have i₂ := b4e104594 X0 X1
               grind)
            | exact superpose b4e104594 b4e16
            | (have j0 := b4e16 X0 X0
               have j1 := b4e104594 X0 X1
               grind)
            | (have r₁ := b4e16 X1 X1
               have r₂ := b4e104594 X1 X1
               grind)
            | (have r₁ := b4e16 X0 X0
               have r₂ := b4e104594 X0 X0
               grind)
            | (have r₁ := b4e16 X1 X0
               have r₂ := b4e104594 X0 X1
               grind)
            | exact resolve b4e16 b4e104594
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e104594
          have b4e116467 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e116010 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e116010
          have b4e116742 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e115879 X0 X1
               have j1 := b4e84195 X1 X0
               grind)
            | (have r₁ := b4e115879 X1 X0
               have r₂ := b4e84195 X0 X1
               grind)
            | (have r₁ := b4e115879 X1 X1
               have r₂ := b4e84195 X1 X1
               grind)
            | (have r₁ := b4e115879 X0 X0
               have r₂ := b4e84195 X0 X0
               grind)
            | exact resolve b4e115879 b4e84195
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e84195 b4e115879
          have b4e116931 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e115302 X0 X1
               have j1 := b4e30836 X0 X1
               grind)
            | (have r₁ := b4e115302 X0 X1
               have r₂ := b4e30836 X0 X1
               grind)
            | (have r₁ := b4e115302 X1 X1
               have r₂ := b4e30836 X1 X1
               grind)
            | exact resolve b4e115302 b4e30836
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30836 b4e115302
          have b4e117090 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e116742 X0 X1
               have j1 := b4e16 X1 X0
               grind)
            | (have r₁ := b4e116742 X1 X0
               have r₂ := b4e16 X0 X1
               grind)
            | (have r₁ := b4e116742 X0 X0
               have r₂ := b4e16 X0 X0
               grind)
            | exact resolve b4e116742 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e116742
          have b4e117183 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e116931 X0 X1
               have j1 := b4e30336 X0 X1
               grind)
            | (have r₁ := b4e116931 X0 X1
               have r₂ := b4e30336 X0 X1
               grind)
            | exact resolve b4e116931 b4e30336
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30336 b4e116931
          have b4e119066 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e117090 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e117090
          have b4e121129 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 X0 X1
               have i₂ := b4e117183 X0 X1
               grind)
            | (have i₁ := b4e17 X0 X0
               have i₂ := b4e117183 X0 X1
               grind)
            | exact superpose b4e117183 b4e17
            | (have j0 := b4e17 X0 X1
               have j1 := b4e117183 X0 X1
               grind)
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e117183 X0 X1
               grind)
            | (have r₁ := b4e17 X1 X1
               have r₂ := b4e117183 X1 X1
               grind)
            | (have r₁ := b4e17 X0 X0
               have r₂ := b4e117183 X0 X0
               grind)
            | exact resolve b4e17 b4e117183
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e121568 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X1 X0
               have i₂ := b4e117183 X1 X0
               grind)
            | (have i₁ := b4e16 X1 X1
               have i₂ := b4e117183 X0 X1
               grind)
            | exact superpose b4e117183 b4e16
            | (have j0 := b4e16 X0 X0
               have j1 := b4e117183 X1 X0
               grind)
            | (have r₁ := b4e16 X0 X0
               have r₂ := b4e117183 X0 X0
               grind)
            | (have r₁ := b4e16 X1 X1
               have r₂ := b4e117183 X1 X1
               grind)
            | (have r₁ := b4e16 X0 X1
               have r₂ := b4e117183 X0 X1
               grind)
            | exact resolve b4e16 b4e117183
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e117183
          have b4e122035 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e121568 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e121568
          have b4e122071 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e121129 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e121129
          have b4e122326 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e122071 X0 X1
               have j1 := b4e119066 X0 X1
               grind)
            | (have r₁ := b4e122071 X0 X1
               have r₂ := b4e119066 X0 X1
               grind)
            | (have r₁ := b4e122071 X1 X0
               have r₂ := b4e119066 X0 X1
               grind)
            | (have r₁ := b4e122071 X0 X0
               have r₂ := b4e119066 X0 X0
               grind)
            | exact resolve b4e122071 b4e119066
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e119066 b4e122071
          have b4e128307 : (τ (M.op x x)) = (τ (M.op x y)) ∨ (M.op y y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e122035 x y
               have i₂ := b4e93077
               grind)
            | exact superpose b4e93077 b4e122035
            | (have j0 := b4e122035 x y
               grind)
            | exact resolve b4e122035 b4e93077
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e93077 b4e122035
          have b4e128566 : (τ (M.op x x)) = (τ (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b4e128307
               have r₂ := b4e26
               grind)
            | exact resolve b4e128307 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e128307
          have b4e130460 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X1 X0
               have i₂ := b4e104920 X1 X0
               grind)
            | (have i₁ := b4e16 X1 X1
               have i₂ := b4e104920 X0 X1
               grind)
            | exact superpose b4e104920 b4e16
            | (have j0 := b4e16 X0 X0
               have j1 := b4e104920 X1 X0
               grind)
            | (have r₁ := b4e16 X0 X0
               have r₂ := b4e104920 X0 X0
               grind)
            | (have r₁ := b4e16 X1 X1
               have r₂ := b4e104920 X1 X1
               grind)
            | (have r₁ := b4e16 X0 X1
               have r₂ := b4e104920 X0 X1
               grind)
            | exact resolve b4e16 b4e104920
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e104920
          have b4e130532 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e130460 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e130460
          have b4e131826 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X1) ∨ (M.op (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e116467 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e116467
          have b4e133831 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X1 X0) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e130532 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e130532
          have b4e134822 : (M.op x y) ≠ (M.op x y) ∨ (τ (M.op x y)) = (M.op (τ x) (τ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b4e131826 y x
               have i₂ := b4e40960
               grind)
            | exact superpose b4e40960 b4e131826
            | (have j0 := b4e131826 y x
               grind)
            | (have r₁ := b4e131826 y x
               have r₂ := b4e40960
               grind)
            | exact resolve b4e131826 b4e40960
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e131826
          have b4e134829 : (M.op x y) ≠ (M.op x y) ∨ (τ (M.op x y)) = (M.op (τ x) (τ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b4e134822
          have b4e134830 : (τ (M.op x y)) = (M.op (τ x) (τ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b4e134829
          have b4e136579 : (τ (M.op x x)) ≠ (τ (M.op x y)) ∨ (M.op (τ y) (τ y)) = (k (τ y) (τ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e242 x (τ y)
               have i₂ := b4e134830
               grind)
            | exact superpose b4e134830 b4e242
            | (have j0 := b4e242 x (τ y)
               grind)
            | exact resolve b4e242 b4e134830
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e134830
          have b4e136588 : (M.op (τ y) (τ y)) = (k (τ y) (τ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b4e136579
               have r₂ := b4e128566
               grind)
            | exact resolve b4e136579 b4e128566
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e128566 b4e136579
          have b4e136590 : (τ (k y x)) = (M.op (τ y) (τ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e136588
               have i₂ := b4e47 x y
               grind)
            | exact superpose b4e47 b4e136588
            | exact resolve b4e136588 b4e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e136588
          have b4e136592 : (τ (M.op y y)) = (τ (k y x)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e136590
               have i₂ := b4e182 y
               grind)
            | exact superpose b4e182 b4e136590
            | exact resolve b4e136590 b4e182
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e136590
          have b4e137514 : (k y x) = (σ (τ (M.op y y))) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e15 (k y x)
               have i₂ := b4e136592
               grind)
            | exact superpose b4e136592 b4e15
            | exact resolve b4e15 b4e136592
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e136592
          have b4e137635 : (M.op y y) = (k y x) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e137514
               have i₂ := b4e15 (M.op y y)
               grind)
            | exact superpose b4e15 b4e137514
            | exact resolve b4e137514 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e137514
          have b4e138578 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e40960
               have i₂ := b4e137635
               grind)
            | exact superpose b4e137635 b4e40960
            | exact resolve b4e40960 b4e137635
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40960 b4e137635
          have b4e138625 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b4e138578
          have b4e173547 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e42 X0 (σ X1)
               have i₂ := b4e85094 X1 (σ X0)
               grind)
            | exact superpose b4e85094 b4e42
            | (have j1 := b4e85094 X1 (σ X0)
               grind)
            | exact resolve b4e42 b4e85094
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42 b4e85094
          have b4e173608 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e173547 X0 X1
               have i₂ := b4e78 X0
               grind)
            | exact superpose b4e78 b4e173547
            | (have j0 := b4e173547 X0 X1
               grind)
            | exact resolve b4e173547 b4e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78 b4e173547
          have b4e173636 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ (σ X1))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e173608 X0 X1
               have i₂ := b4e14 (M.op X0 X0)
               grind)
            | exact superpose b4e14 b4e173608
            | (have j0 := b4e173608 X0 X1
               grind)
            | exact resolve b4e173608 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e173608
          have b4e173653 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e173636 X0 X1
               have i₂ := b4e14 X1
               grind)
            | exact superpose b4e14 b4e173636
            | (have j0 := b4e173636 X0 X1
               grind)
            | exact resolve b4e173636 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e173636
          have b4e173666 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e173653 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e173653
            | (have j0 := b4e173653 X0 X1
               grind)
            | exact resolve b4e173653 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e173653
          have b4e173671 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e173666 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e173666
            | (have j0 := b4e173666 X0 X1
               grind)
            | exact resolve b4e173666 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e173666
          have b4e177013 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e173671 y x
               grind)
            | exact superpose b4e173671 b4e20
            | (have j1 := b4e173671 y x
               grind)
            | exact resolve b4e20 b4e173671
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e173671
          have b4e180530 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b4e177013
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e177013
            | (have j1 := b4e18 y x
               grind)
            | exact resolve b4e177013 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e180536 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b4e177013
               have i₂ := b4e13648 y x
               grind)
            | exact superpose b4e13648 b4e177013
            | (have j1 := b4e13648 y x
               grind)
            | (have r₁ := b4e177013
               have r₂ := b4e13648 y x
               grind)
            | exact resolve b4e177013 b4e13648
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13648 b4e177013
          have b4e180543 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) ∨ (M.op x y) = (M.op x x) := by grind
          clear b4e180536
          have b4e180544 : (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) ∨ (M.op x y) = (M.op x x) := by grind
          clear b4e180543
          have b4e180549 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b4e180530
          have b4e180550 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
          clear b4e180549
          have b4e180558 : (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) := by
            first
            | (have j1 := b4e16 y x
               grind)
            | (have r₁ := b4e180544
               have r₂ := b4e16 y x
               grind)
            | exact resolve b4e180544 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e180544
          have b4e184543 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b4e1053
               have i₂ := b4e180558
               grind)
            | exact superpose b4e180558 b4e1053
            | exact resolve b4e1053 b4e180558
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1053
          have b4e184578 : (τ (M.op y y)) = (τ (M.op x y)) ∨ (M.op y y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b4e122326 y x
               have i₂ := b4e180558
               grind)
            | exact superpose b4e180558 b4e122326
            | (have j0 := b4e122326 y x
               grind)
            | exact resolve b4e122326 b4e180558
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e122326 b4e180558
          have b4e184599 : (M.op x x) = (k y x) ∨ x = y ∨ (M.op x y) = (M.op y y) := by grind
          clear b4e184543
          have b4e184605 : (τ (M.op y y)) = (τ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) := by
            first
            | (have r₁ := b4e184578
               have r₂ := b4e26
               grind)
            | exact resolve b4e184578 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26 b4e184578
          have b4e185460 : (M.op x y) ≠ (M.op x x) ∨ (τ (M.op x x)) = (M.op (τ x) (τ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b4e133831 y x
               have i₂ := b4e184599
               grind)
            | exact superpose b4e184599 b4e133831
            | (have j0 := b4e133831 y x
               grind)
            | exact resolve b4e133831 b4e184599
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e133831
          have b4e185462 : (M.op x y) ≠ (M.op x x) ∨ (τ (M.op x x)) = (M.op (τ x) (τ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
          clear b4e185460
          have b4e185493 : (τ (M.op x x)) = (M.op (τ x) (τ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
            first
            | (have r₁ := b4e185462
               have r₂ := b4e180550
               grind)
            | exact resolve b4e185462 b4e180550
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e180550 b4e185462
          have b4e191062 : (τ (M.op x x)) ≠ (τ (M.op x x)) ∨ (M.op (τ y) (τ y)) = (k (τ y) (τ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b4e242 x (τ y)
               have i₂ := b4e185493
               grind)
            | exact superpose b4e185493 b4e242
            | (have j0 := b4e242 x (τ y)
               grind)
            | (have r₁ := b4e242 x (τ y)
               have r₂ := b4e185493
               grind)
            | exact resolve b4e242 b4e185493
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e242 b4e185493
          have b4e191066 : (M.op (τ y) (τ y)) = (k (τ y) (τ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
          clear b4e191062
          have b4e191080 : (τ (k y x)) = (M.op (τ y) (τ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b4e191066
               have i₂ := b4e47 x y
               grind)
            | exact superpose b4e47 b4e191066
            | exact resolve b4e191066 b4e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e47 b4e191066
          have b4e191086 : (τ (M.op y y)) = (τ (k y x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b4e191080
               have i₂ := b4e182 y
               grind)
            | exact superpose b4e182 b4e191080
            | exact resolve b4e191080 b4e182
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e182 b4e191080
          have b4e192428 : (τ (M.op x x)) = (τ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ x = y ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b4e191086
               have i₂ := b4e184599
               grind)
            | exact superpose b4e184599 b4e191086
            | exact resolve b4e191086 b4e184599
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e184599 b4e191086
          have b4e192505 : (τ (M.op x x)) = (τ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
          clear b4e192428
          have b4e223495 : (τ (M.op x x)) = (τ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b4e184605
               have i₂ := b4e192505
               grind)
            | exact superpose b4e192505 b4e184605
            | exact resolve b4e184605 b4e192505
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e184605 b4e192505
          have b4e223517 : (τ (M.op x x)) = (τ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) ∨ x = y := by
            first
            | (have j1 := b4e17 y x
               grind)
            | (have r₁ := b4e223495
               have r₂ := b4e17 y x
               grind)
            | exact resolve b4e223495 b4e17
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e223495
          have b4e223519 : (τ (M.op x x)) = (τ (M.op x y)) ∨ (M.op x x) = (k y x) ∨ x = y := by
            first
            | (have r₁ := b4e223517
               have r₂ := b4e38258
               grind)
            | exact resolve b4e223517 b4e38258
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e223517
          have b4e226114 : (M.op x y) = (σ (τ (M.op x x))) ∨ (M.op x x) = (k y x) ∨ x = y := by
            first
            | (have i₁ := b4e15 (M.op x y)
               have i₂ := b4e223519
               grind)
            | exact superpose b4e223519 b4e15
            | exact resolve b4e15 b4e223519
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e223519
          have b4e226226 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) ∨ x = y := by
            first
            | (have i₁ := b4e226114
               have i₂ := b4e15 (M.op x x)
               grind)
            | exact superpose b4e15 b4e226114
            | exact resolve b4e226114 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e226114
          have b4e226227 : (M.op x x) = (k y x) ∨ x = y := by
            first
            | (have r₁ := b4e226226
               have r₂ := b4e38258
               grind)
            | exact resolve b4e226226 b4e38258
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38258 b4e226226
          have b4e228879 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = y := by
            first
            | (have i₁ := b4e2760 x y
               have i₂ := b4e226227
               grind)
            | exact superpose b4e226227 b4e2760
            | (have j0 := b4e2760 x y
               grind)
            | exact resolve b4e2760 b4e226227
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2760 b4e226227
          have b4e228901 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = y := by grind
          clear b4e228879
          have b4e271331 : (σ (M.op y y)) = (σ (k y x)) ∨ (σ (M.op x x)) = (σ (k y x)) ∨ x = y ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e228901
               have i₂ := b4e1068
               grind)
            | exact superpose b4e1068 b4e228901
            | exact resolve b4e228901 b4e1068
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1068 b4e228901
          have b4e271355 : (σ (M.op y y)) = (σ (k y x)) ∨ x = y ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have j1 := b4e2968 y x
               grind)
            | (have r₁ := b4e271331
               have r₂ := b4e2968 y x
               grind)
            | exact resolve b4e271331 b4e2968
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2968 b4e271331
          have b4e271359 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = y ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b4e271355
               have r₂ := b4e8634
               grind)
            | exact resolve b4e271355 b4e8634
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8634 b4e271355
          have b4e271945 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ x = y ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e271359
               grind)
            | exact superpose b4e271359 b4e20
            | exact resolve b4e20 b4e271359
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e271359
          have b4e272120 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e271945
               have i₂ := b4e138625
               grind)
            | exact superpose b4e138625 b4e271945
            | exact resolve b4e271945 b4e138625
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e138625 b4e271945
          have b4e272126 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
          clear b4e272120
          have b4e272127 : (σ x) = (σ y) ∨ x = y := by grind
          clear b4e272126
          have b4e272517 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ x = y := by
            first
            | (have i₁ := b4e25
               have i₂ := b4e272127
               grind)
            | exact superpose b4e272127 b4e25
            | exact resolve b4e25 b4e272127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25 b4e272127
          have b4e272672 : x = y := by grind
          clear b4e272517
          have b4e273155 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e165
               have i₂ := b4e272672
               grind)
            | exact superpose b4e272672 b4e165
            | exact resolve b4e165 b4e272672
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e165 b4e272672
          have b4e273199 : False := by grind
          exact b4e273199
        · have b5e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op y x) ≠ (M.op y y) := by grind
          have b5e22 : (M.op y x) = (M.op x x) := by grind
          have b5e23 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          have b5e24 : (M.op (σ y) (σ x)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : (M.op y y) ≠ (M.op x x) := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e21
            | exact resolve b5e21 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e66 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e64 (σ X0)
               grind)
            | exact superpose b5e64 b5e19
            | exact resolve b5e19 b5e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e75 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e66 X0
               have i₂ := b5e64 X0
               grind)
            | exact superpose b5e64 b5e66
            | exact resolve b5e66 b5e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e64 b5e66
          have b5e83 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (M.op x x) ∨ (M.op y y) = (k x y) := by
            first
            | (have i₁ := b5e17 x y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e17
            | (have j0 := b5e17 x x
               grind)
            | (have r₁ := b5e17 x y
               have r₂ := b5e22
               grind)
            | exact resolve b5e17 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e86 : (M.op y y) = (M.op x x) ∨ (M.op y y) = (k x y) := by grind
          clear b5e83
          have b5e87 : (M.op y y) = (k x y) := by
            first
            | (have r₁ := b5e86
               have r₂ := b5e25
               grind)
            | exact resolve b5e86 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e86
          have b5e103 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e23
               have i₂ := b5e18 X0 (σ y)
               grind)
            | (have i₁ := b5e23
               have i₂ := b5e18 (σ y) (σ y)
               grind)
            | exact superpose b5e18 b5e23
            | (have j1 := b5e18 X0 (σ y)
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | exact resolve b5e23 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e143 : (M.op (σ y) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e75 y
               grind)
            | exact superpose b5e75 b5e23
            | exact resolve b5e23 b5e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e75
          have b5e1395 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e103 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e103
          have b5e1396 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1395
               have r₂ := b5e24
               grind)
            | exact resolve b5e1395 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1395
          have b5e1397 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1396
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1396
            | exact resolve b5e1396 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1396
          have b5e1398 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e1397
               have i₂ := b5e87
               grind)
            | exact superpose b5e87 b5e1397
            | exact resolve b5e1397 b5e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e87 b5e1397
          have b5e1399 : False := by grind
          exact b5e1399
    · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op y x) ≠ (M.op y y) := by grind
        have b6e21 : (M.op y x) ≠ (M.op x x) := by grind
        have b6e22 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e49 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e15
          | (have j0 := b6e15 (σ y) (σ y)
             grind)
          | (have r₁ := b6e15 (σ x) (σ y)
             have r₂ := b6e22
             grind)
          | exact resolve b6e15 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e50 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e51 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear b6e49
        have b6e52 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e51
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e51
          | exact resolve b6e51 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51
        have b6e71 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ x)
             have i₂ := b6e52
             grind)
          | exact superpose b6e52 b6e15
          | exact resolve b6e15 b6e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e52
        have b6e74 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
        clear b6e71
        have b6e77 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b6e74
             have i₂ := b6e18 x x
             grind)
          | exact superpose b6e18 b6e74
          | exact resolve b6e74 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e74
        have b6e78 : (σ (k x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e77
             have i₂ := b6e50 x
             grind)
          | exact superpose b6e50 b6e77
          | exact resolve b6e77 b6e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e50 b6e77
        have b6e133 : (k x y) = (τ (σ (M.op x x))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e78
             grind)
          | exact superpose b6e78 b6e13
          | exact resolve b6e13 b6e78
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e78
        have b6e134 : (M.op x x) = (k x y) := by
          first
          | (have i₁ := b6e133
             have i₂ := b6e13 (M.op x x)
             grind)
          | exact superpose b6e13 b6e133
          | exact resolve b6e133 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e133
        have b6e153 : (M.op y x) = (M.op x x) ∨ (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op x x) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e134
             grind)
          | exact superpose b6e134 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e134
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e134
        have b6e154 : (M.op y x) = (M.op x x) ∨ (M.op y x) = (M.op y y) := by grind
        clear b6e153
        have b6e156 : (M.op y x) = (M.op y y) := by
          first
          | (have r₁ := b6e154
             have r₂ := b6e21
             grind)
          | exact resolve b6e154 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e154
        have b6e158 : False := by grind
        exact b6e158
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : (M.op y x) ≠ (M.op y y) := by grind
          have b7e22 : (M.op y x) ≠ (M.op x x) := by grind
          have b7e23 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e66 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e64 (σ X0)
               grind)
            | exact superpose b7e64 b7e19
            | exact resolve b7e19 b7e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e75 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e66 X0
               have i₂ := b7e64 X0
               grind)
            | exact superpose b7e64 b7e66
            | exact resolve b7e66 b7e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64 b7e66
          have b7e84 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e17 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e17
            | (have j0 := b7e17 (σ x) (σ x)
               grind)
            | (have r₁ := b7e17 (σ x) (σ y)
               have r₂ := b7e24
               grind)
            | exact resolve b7e17 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e86 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b7e84
          have b7e87 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e86
               have r₂ := b7e25
               grind)
            | exact resolve b7e86 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e86
          have b7e88 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e87
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e87
            | exact resolve b7e87 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e87
          have b7e89 : (σ (k x y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e88
               have i₂ := b7e75 y
               grind)
            | exact superpose b7e75 b7e88
            | exact resolve b7e88 b7e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e75 b7e88
          have b7e94 : (k x y) = (τ (σ (M.op y y))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e89
               grind)
            | exact superpose b7e89 b7e14
            | exact resolve b7e14 b7e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e89
          have b7e95 : (M.op y y) = (k x y) := by
            first
            | (have i₁ := b7e94
               have i₂ := b7e14 (M.op y y)
               grind)
            | exact superpose b7e14 b7e94
            | exact resolve b7e94 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e94
          have b7e152 : (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op x x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e95
               grind)
            | exact superpose b7e95 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e95
          have b7e153 : (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op x x) := by grind
          clear b7e152
          have b7e155 : (M.op y x) = (M.op x x) := by
            first
            | (have r₁ := b7e153
               have r₂ := b7e21
               grind)
            | exact resolve b7e153 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e153
          have b7e157 : False := by grind
          exact b7e157
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 (τ X0) X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e19
            | exact resolve b8e19 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b8e30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e14 (k (τ X0) X1)
               have i₂ := b8e25 X0 X1
               grind)
            | exact superpose b8e25 b8e14
            | exact resolve b8e14 b8e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e14 (k X0 (τ X1))
               have i₂ := b8e26 X1 X0
               grind)
            | exact superpose b8e26 b8e14
            | exact resolve b8e14 b8e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e41 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e30 X1 (τ X0)
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e30
            | exact resolve b8e30 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e61 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e63 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e61 (σ X0)
               grind)
            | exact superpose b8e61 b8e19
            | exact resolve b8e19 b8e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e66 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
            intro X0
            first
            | (have i₁ := b8e26 X0 (τ X0)
               have i₂ := b8e61 (τ X0)
               grind)
            | exact superpose b8e61 b8e26
            | exact resolve b8e26 b8e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e69 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e66 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e66
            | exact resolve b8e66 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66
          have b8e72 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e63 X0
               have i₂ := b8e61 X0
               grind)
            | exact superpose b8e61 b8e63
            | exact resolve b8e63 b8e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e63
          have b8e75 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e69 X0
               have i₂ := b8e61 X0
               grind)
            | exact superpose b8e61 b8e69
            | exact resolve b8e69 b8e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61 b8e69
          have b8e90 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X1 (σ X0)
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e16
            | (have j0 := b8e16 X1 (σ X0)
               grind)
            | exact resolve b8e16 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e102 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X1 X0
               have i₂ := b8e18 X1 X0
               grind)
            | (have i₁ := b8e16 X1 X1
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X0 X0
               have j1 := b8e18 X1 X0
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | (have r₁ := b8e16 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e113 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
            | (have r₁ := b8e17 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | (have r₁ := b8e17 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | (have r₁ := b8e17 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | exact resolve b8e17 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e125 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
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
          have b8e131 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e18 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e133 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e113 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e113
          have b8e135 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e102 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e102
          have b8e138 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e125 X0 X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e125
            | (have j0 := b8e125 X0 X1
               grind)
            | exact resolve b8e125 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e125
          have b8e140 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e133 X0 X1
               have j1 := b8e131 X1 X0
               grind)
            | (have r₁ := b8e133 X0 X1
               have r₂ := b8e131 X0 X1
               grind)
            | (have r₁ := b8e133 X1 X0
               have r₂ := b8e131 X0 X1
               grind)
            | (have r₁ := b8e133 X0 X0
               have r₂ := b8e131 X0 X0
               grind)
            | exact resolve b8e133 b8e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e131 b8e133
          have b8e143 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e138 X0 X1
               have i₂ := b8e72 X1
               grind)
            | exact superpose b8e72 b8e138
            | (have j0 := b8e138 X0 X1
               grind)
            | exact resolve b8e138 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e138
          have b8e155 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e14 (M.op (τ X0) (τ X0))
               have i₂ := b8e75 X0
               grind)
            | exact superpose b8e75 b8e14
            | exact resolve b8e14 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e252 : ∀ X0 X1 : G, (M.op (τ X0) X1) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X1 (τ X0)
               have i₂ := b8e155 X0
               grind)
            | exact superpose b8e155 b8e16
            | (have j0 := b8e16 X1 (τ X0)
               grind)
            | exact resolve b8e16 b8e155
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e345 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X0 X1
               have i₂ := b8e135 (τ X0) X1
               grind)
            | exact superpose b8e135 b8e26
            | (have j1 := b8e135 (τ X0) X1
               grind)
            | exact resolve b8e26 b8e135
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e135
          have b8e424 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e140 (σ X0) (σ X1)
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e140
            | (have j0 := b8e140 (σ X0) (σ X1)
               grind)
            | exact resolve b8e140 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e462 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X0 X1
               have i₂ := b8e140 X1 (τ X0)
               grind)
            | exact superpose b8e140 b8e26
            | (have j1 := b8e140 X1 (τ X0)
               grind)
            | exact resolve b8e26 b8e140
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26
          have b8e465 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e25 X1 X0
               have i₂ := b8e140 (τ X1) X0
               grind)
            | exact superpose b8e140 b8e25
            | (have j1 := b8e140 (τ X1) X0
               grind)
            | exact resolve b8e25 b8e140
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e140
          have b8e482 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e462 X0 X1
               have i₂ := b8e75 X0
               grind)
            | exact superpose b8e75 b8e462
            | (have j0 := b8e462 X0 X1
               grind)
            | exact resolve b8e462 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e462
          have b8e493 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e424 X0 X1
               have i₂ := b8e72 X1
               grind)
            | exact superpose b8e72 b8e424
            | (have j0 := b8e424 X0 X1
               grind)
            | exact resolve b8e424 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e424
          have b8e501 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e482 X0 X1
               have i₂ := b8e155 X0
               grind)
            | exact superpose b8e155 b8e482
            | (have j0 := b8e482 X0 X1
               grind)
            | exact resolve b8e482 b8e155
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e155 b8e482
          have b8e507 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e493 X0 X1
               have i₂ := b8e72 X1
               grind)
            | exact superpose b8e72 b8e493
            | (have j0 := b8e493 X0 X1
               grind)
            | exact resolve b8e493 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e493
          have b8e1976 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 (σ X0) (σ X1)
               have i₂ := b8e143 X1 X0
               grind)
            | exact superpose b8e143 b8e16
            | (have j0 := b8e16 (σ X0) (σ X1)
               have j1 := b8e143 X1 X0
               grind)
            | exact resolve b8e16 b8e143
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1999 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e143 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e143
          have b8e2061 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b8e1976 X0 X1
               have j1 := b8e90 X1 (σ X0)
               grind)
            | (have r₁ := b8e1976 X0 X0
               have r₂ := b8e90 X0 (σ X0)
               grind)
            | (have r₁ := b8e1976 X0 X0
               have r₂ := b8e90 X0 (σ X0)
               grind)
            | exact resolve b8e1976 b8e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e90 b8e1976
          have b8e2130 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e2061 X0 X1
               have i₂ := b8e72 X1
               grind)
            | exact superpose b8e72 b8e2061
            | (have j0 := b8e2061 X0 X1
               grind)
            | exact resolve b8e2061 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2061
          have b8e2179 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e2130 X0 X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e2130
            | (have j0 := b8e2130 X0 X1
               grind)
            | exact resolve b8e2130 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2130
          have b8e2210 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e2179 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e2179
            | (have j0 := b8e2179 X0 X1
               grind)
            | exact resolve b8e2179 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2179
          have b8e6417 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e345 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e345
            | exact resolve b8e345 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e345
          have b8e6626 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e6417 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e6417
            | (have j0 := b8e6417 X0 X1
               grind)
            | exact resolve b8e6417 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6417
          have b8e7931 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e465 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e465
            | exact resolve b8e465 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e465
          have b8e8173 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e7931 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e7931
            | (have j0 := b8e7931 X0 X1
               grind)
            | exact resolve b8e7931 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7931
          have b8e8503 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e252 X0 X1
               have i₂ := b8e501 X0 X1
               grind)
            | exact superpose b8e501 b8e252
            | (have j0 := b8e252 X0 X1
               have j1 := b8e501 X0 X1
               grind)
            | (have r₁ := b8e252 X0 X1
               have r₂ := b8e501 X0 X1
               grind)
            | exact resolve b8e252 b8e501
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e252
          have b8e8552 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e15 (M.op X0 X0)
               have i₂ := b8e501 X0 X1
               grind)
            | exact superpose b8e501 b8e15
            | (have j1 := b8e501 X0 X1
               grind)
            | exact resolve b8e15 b8e501
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e501
          have b8e8698 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have j0 := b8e8503 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8503
          have b8e13723 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e2210 (τ X1) (τ X0)
               have i₂ := b8e41 X0 X1
               grind)
            | exact superpose b8e41 b8e2210
            | (have j0 := b8e2210 (τ X0) (τ X1)
               grind)
            | exact resolve b8e2210 b8e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e13811 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e13723 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e13723
            | (have j0 := b8e13723 X0 X1
               grind)
            | exact resolve b8e13723 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13723
          have b8e13840 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e13811 X0 X1
               have i₂ := b8e75 X1
               grind)
            | exact superpose b8e75 b8e13811
            | (have j0 := b8e13811 X0 X1
               grind)
            | exact resolve b8e13811 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13811
          have b8e13865 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e13840 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e13840
            | (have j0 := b8e13840 X0 X1
               grind)
            | exact resolve b8e13840 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13840
          have b8e13880 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e13865 X0 X1
               have i₂ := b8e75 X0
               grind)
            | exact superpose b8e75 b8e13865
            | (have j0 := b8e13865 X0 X1
               grind)
            | exact resolve b8e13865 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13865
          have b8e13889 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e13880 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e13880
            | (have j0 := b8e13880 X0 X1
               grind)
            | exact resolve b8e13880 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13880
          have b8e13893 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e13889 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e13889
            | (have j0 := b8e13889 X0 X1
               grind)
            | exact resolve b8e13889 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13889
          have b8e13894 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e13893 X0 X1
               have i₂ := b8e75 X0
               grind)
            | exact superpose b8e75 b8e13893
            | (have j0 := b8e13893 X0 X1
               grind)
            | exact resolve b8e13893 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13893
          have b8e15924 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e17 (σ X0) (σ X1)
               have i₂ := b8e507 X0 X1
               grind)
            | exact superpose b8e507 b8e17
            | (have j0 := b8e17 (σ X0) (σ X1)
               have j1 := b8e507 X0 X1
               grind)
            | exact resolve b8e17 b8e507
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e16099 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e15924 X0 X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e15924
            | (have j0 := b8e15924 X0 X1
               grind)
            | exact resolve b8e15924 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15924
          have b8e16236 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e16099 X0 X1
               have i₂ := b8e72 X1
               grind)
            | exact superpose b8e72 b8e16099
            | (have j0 := b8e16099 X0 X1
               grind)
            | exact resolve b8e16099 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16099
          have b8e16237 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e16236 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16236
          have b8e16334 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e16237 X0 X1
               have i₂ := b8e72 X1
               grind)
            | exact superpose b8e72 b8e16237
            | (have j0 := b8e16237 X0 X1
               grind)
            | exact resolve b8e16237 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16237
          have b8e16369 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e16334 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e16334
            | (have j0 := b8e16334 X0 X1
               grind)
            | exact resolve b8e16334 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16334
          have b8e16370 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e16369 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16369
          have b8e22799 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e1999 (τ X0) (τ X1)
               have i₂ := b8e41 X0 X1
               grind)
            | exact superpose b8e41 b8e1999
            | (have j0 := b8e1999 (τ X1) (τ X0)
               grind)
            | exact resolve b8e1999 b8e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e22914 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e22799 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e22799
            | (have j0 := b8e22799 X0 X1
               grind)
            | exact resolve b8e22799 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e22799
          have b8e22958 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e22914 X0 X1
               have i₂ := b8e75 X1
               grind)
            | exact superpose b8e75 b8e22914
            | (have j0 := b8e22914 X0 X1
               grind)
            | exact resolve b8e22914 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e22914
          have b8e22992 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e22958 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e22958
            | (have j0 := b8e22958 X0 X1
               grind)
            | exact resolve b8e22958 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e22958
          have b8e23019 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e22992 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e22992
            | (have j0 := b8e22992 X0 X1
               grind)
            | exact resolve b8e22992 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e22992
          have b8e23044 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e23019 X0 X1
               have i₂ := b8e75 X0
               grind)
            | exact superpose b8e75 b8e23019
            | (have j0 := b8e23019 X0 X1
               grind)
            | exact resolve b8e23019 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23019
          have b8e23066 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e23044 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e23044
            | (have j0 := b8e23044 X0 X1
               grind)
            | exact resolve b8e23044 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23044
          have b8e23075 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e23066 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e23066
            | (have j0 := b8e23066 X0 X1
               grind)
            | exact resolve b8e23066 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23066
          have b8e23084 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e23075 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e23075
            | (have j0 := b8e23075 X0 X1
               grind)
            | exact resolve b8e23075 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23075
          have b8e90934 : ∀ X0 X1 : G, (k X0 (σ (τ X1))) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e25 X0 (τ X1)
               have i₂ := b8e8698 X1 (τ X0)
               grind)
            | exact superpose b8e8698 b8e25
            | (have j1 := b8e8698 X1 (τ X0)
               grind)
            | exact resolve b8e25 b8e8698
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25
          have b8e91369 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e30 (σ X1) X0
               have i₂ := b8e8698 (σ X0) X1
               grind)
            | exact superpose b8e8698 b8e30
            | (have j1 := b8e8698 (σ X0) X1
               grind)
            | exact resolve b8e30 b8e8698
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8698
          have b8e91619 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e91369 X0 X1
               have i₂ := b8e14 X1
               grind)
            | exact superpose b8e14 b8e91369
            | (have j0 := b8e91369 X0 X1
               grind)
            | exact resolve b8e91369 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e91369
          have b8e91793 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ (τ X1))) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e90934 X0 X1
               have i₂ := b8e75 X0
               grind)
            | exact superpose b8e75 b8e90934
            | (have j0 := b8e90934 X0 X1
               grind)
            | exact resolve b8e90934 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e75 b8e90934
          have b8e92072 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e91619 X0 X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e91619
            | (have j0 := b8e91619 X0 X1
               grind)
            | exact resolve b8e91619 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e91619
          have b8e92158 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e91793 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e91793
            | (have j0 := b8e91793 X0 X1
               grind)
            | exact resolve b8e91793 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e91793
          have b8e92321 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e92072 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e92072
            | (have j0 := b8e92072 X0 X1
               grind)
            | exact resolve b8e92072 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e92072
          have b8e92386 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e92158 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e92158
            | (have j0 := b8e92158 X0 X1
               grind)
            | exact resolve b8e92158 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e92158
          have b8e92487 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e92321 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e92321
            | (have j0 := b8e92321 X0 X1
               grind)
            | exact resolve b8e92321 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e92321
          have b8e92539 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e92386 X0 X1
               have i₂ := b8e41 X1 X0
               grind)
            | exact superpose b8e41 b8e92386
            | (have j0 := b8e92386 X0 X1
               grind)
            | exact resolve b8e92386 b8e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e41 b8e92386
          have b8e92587 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e92487 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e92487
            | (have j0 := b8e92487 X0 X1
               grind)
            | exact resolve b8e92487 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e92487
          have b8e94181 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e30 X1 X0
               have i₂ := b8e92587 (σ X0) X1
               grind)
            | exact superpose b8e92587 b8e30
            | (have j1 := b8e92587 (σ X0) X1
               grind)
            | exact resolve b8e30 b8e92587
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e92587
          have b8e94681 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e94181 X0 X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e94181
            | (have j0 := b8e94181 X0 X1
               grind)
            | exact resolve b8e94181 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e94181
          have b8e95316 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e94681 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e94681
            | (have j0 := b8e94681 X0 X1
               grind)
            | exact resolve b8e94681 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e94681
          have b8e105682 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e92539 X0 X1
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e92539
            | (have j1 := b8e18 X1 X0
               grind)
            | exact resolve b8e92539 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e106536 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e13894 X0 X1
               have i₂ := b8e92539 X0 X1
               grind)
            | exact superpose b8e92539 b8e13894
            | (have j0 := b8e13894 X1 X0
               have j1 := b8e92539 X1 X0
               grind)
            | (have r₁ := b8e13894 X0 X1
               have r₂ := b8e92539 X0 X1
               grind)
            | (have r₁ := b8e13894 X1 X1
               have r₂ := b8e92539 X1 X1
               grind)
            | exact resolve b8e13894 b8e92539
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e107293 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e92539 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e92539
          have b8e107365 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e106536 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e106536
          have b8e107646 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e105682 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e105682
          have b8e108188 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e107365 X0 X1
               have j1 := b8e107293 X1 X0
               grind)
            | (have r₁ := b8e107365 X0 X1
               have r₂ := b8e107293 X0 X1
               grind)
            | (have r₁ := b8e107365 X1 X0
               have r₂ := b8e107293 X0 X1
               grind)
            | (have r₁ := b8e107365 X0 X0
               have r₂ := b8e107293 X0 X0
               grind)
            | exact resolve b8e107365 b8e107293
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e107293 b8e107365
          have b8e112581 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e107646 (σ X1) (σ X0)
               have i₂ := b8e507 X0 X1
               grind)
            | exact superpose b8e507 b8e107646
            | (have j1 := b8e507 X0 X1
               grind)
            | exact resolve b8e107646 b8e507
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e507 b8e107646
          have b8e114163 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e112581 X0 X1
               have i₂ := b8e72 X1
               grind)
            | exact superpose b8e72 b8e112581
            | (have j0 := b8e112581 X0 X1
               grind)
            | exact resolve b8e112581 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e112581
          have b8e114164 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e114163 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e114163
          have b8e114429 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e114164 X0 X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e114164
            | (have j0 := b8e114164 X0 X1
               grind)
            | exact resolve b8e114164 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e114164
          have b8e114574 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e114429 X0 X1
               have j1 := b8e16370 X0 X1
               grind)
            | (have r₁ := b8e114429 X0 X1
               have r₂ := b8e16370 X0 X1
               grind)
            | (have r₁ := b8e114429 X0 X0
               have r₂ := b8e16370 X0 X0
               grind)
            | exact resolve b8e114429 b8e16370
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16370 b8e114429
          have b8e114621 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) X0) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e114574 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e114574
            | (have j0 := b8e114574 X0 X1
               grind)
            | exact resolve b8e114574 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e114574
          have b8e114637 : ∀ X0 X1 : G, (M.op X1 X0) = (τ (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e114621 X0 X1
               have i₂ := b8e14 X1
               grind)
            | exact superpose b8e14 b8e114621
            | (have j0 := b8e114621 X0 X1
               grind)
            | exact resolve b8e114621 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e114621
          have b8e114648 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e114637 X0 X1
               have i₂ := b8e14 (k X0 X1)
               grind)
            | exact superpose b8e14 b8e114637
            | (have j0 := b8e114637 X0 X1
               grind)
            | exact resolve b8e114637 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e114637
          have b8e131772 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (k X1 (σ X0))) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e108188 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e108188
            | (have j0 := b8e108188 (σ X0) X1
               grind)
            | exact resolve b8e108188 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e108188
          have b8e131839 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e131772 X0 X1
               have i₂ := b8e30 X1 X0
               grind)
            | exact superpose b8e30 b8e131772
            | (have j0 := b8e131772 X0 X1
               grind)
            | exact resolve b8e131772 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30 b8e131772
          have b8e160795 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e38 X0 (σ X1)
               have i₂ := b8e95316 X1 (σ X0)
               grind)
            | exact superpose b8e95316 b8e38
            | (have j1 := b8e95316 X1 (σ X0)
               grind)
            | exact resolve b8e38 b8e95316
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e95316
          have b8e160856 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e160795 X0 X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e160795
            | (have j0 := b8e160795 X0 X1
               grind)
            | exact resolve b8e160795 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e160795
          have b8e160884 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ (σ X1))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e160856 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e160856
            | (have j0 := b8e160856 X0 X1
               grind)
            | exact resolve b8e160856 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e160856
          have b8e160901 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e160884 X0 X1
               have i₂ := b8e14 X1
               grind)
            | exact superpose b8e14 b8e160884
            | (have j0 := b8e160884 X0 X1
               grind)
            | exact resolve b8e160884 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e160884
          have b8e160914 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e160901 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e160901
            | (have j0 := b8e160901 X0 X1
               grind)
            | exact resolve b8e160901 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e160901
          have b8e160919 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e160914 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e160914
            | (have j0 := b8e160914 X0 X1
               grind)
            | exact resolve b8e160914 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e160914
          have b8e164567 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e160919 y x
               grind)
            | exact superpose b8e160919 b8e20
            | (have j1 := b8e160919 y x
               grind)
            | exact resolve b8e20 b8e160919
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e160919
          have b8e165187 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) ∨ (M.op y y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e164567
               have i₂ := b8e6626 x y
               grind)
            | exact superpose b8e6626 b8e164567
            | (have j1 := b8e6626 x y
               grind)
            | (have r₁ := b8e164567
               have r₂ := b8e6626 x y
               grind)
            | exact resolve b8e164567 b8e6626
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6626
          have b8e165189 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e164567
               have i₂ := b8e8173 y x
               grind)
            | exact superpose b8e8173 b8e164567
            | (have j1 := b8e8173 y x
               grind)
            | (have r₁ := b8e164567
               have r₂ := b8e8173 y x
               grind)
            | exact resolve b8e164567 b8e8173
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e164567
          have b8e165196 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) ∨ (M.op x y) = (M.op x x) := by grind
          clear b8e165189
          have b8e165197 : (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) ∨ (M.op x y) = (M.op x x) := by grind
          clear b8e165196
          have b8e165198 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e165187
          have b8e165199 : (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e165198
          have b8e165205 : (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) := by
            first
            | (have j1 := b8e16 y x
               grind)
            | (have r₁ := b8e165197
               have r₂ := b8e16 y x
               grind)
            | exact resolve b8e165197 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e165197
          have b8e165206 : (M.op y y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have j1 := b8e13894 y x
               grind)
            | (have r₁ := b8e165199
               have r₂ := b8e13894 y x
               grind)
            | exact resolve b8e165199 b8e13894
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13894 b8e165199
          have b8e171530 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b8e8173 y x
               have i₂ := b8e165205
               grind)
            | exact superpose b8e165205 b8e8173
            | (have j0 := b8e8173 y x
               grind)
            | exact resolve b8e8173 b8e165205
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8173
          have b8e171547 : (M.op y y) ≠ (M.op x x) ∨ (M.op x x) = (k y x) := by grind
          clear b8e165205
          have b8e171566 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) := by
            first
            | (have r₁ := b8e171530
               have r₂ := b8e171547
               grind)
            | exact resolve b8e171530 b8e171547
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e171530 b8e171547
          have b8e171939 : (M.op y y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e23084 y x
               have i₂ := b8e165206
               grind)
            | exact superpose b8e165206 b8e23084
            | (have j0 := b8e23084 y x
               grind)
            | exact resolve b8e23084 b8e165206
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23084
          have b8e171963 : (M.op y y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e171939
          have b8e219462 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X0))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e38 X0 (σ X1)
               have i₂ := b8e131839 X1 (σ X0)
               grind)
            | exact superpose b8e131839 b8e38
            | (have j1 := b8e131839 X1 (σ X0)
               grind)
            | exact resolve b8e38 b8e131839
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e38 b8e131839
          have b8e219467 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (σ (M.op X0 X0))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e219462 X0 X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e219462
            | (have j0 := b8e219462 X0 X1
               grind)
            | exact resolve b8e219462 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e219462
          have b8e219485 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e219467 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e219467
            | (have j0 := b8e219467 X0 X1
               grind)
            | exact resolve b8e219467 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e219467
          have b8e219496 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e219485 X0 X1
               have i₂ := b8e14 X1
               grind)
            | exact superpose b8e14 b8e219485
            | (have j0 := b8e219485 X0 X1
               grind)
            | exact resolve b8e219485 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e219485
          have b8e219502 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e219496 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e219496
            | (have j0 := b8e219496 X0 X1
               grind)
            | exact resolve b8e219496 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e219496
          have b8e219503 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e219502 X0 X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e219502
            | (have j0 := b8e219502 X0 X1
               grind)
            | exact resolve b8e219502 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e219502
          have b8e226883 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (k y x) ∨ (M.op y y) = (k y x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e219503 y x
               grind)
            | exact superpose b8e219503 b8e20
            | (have j1 := b8e219503 y x
               grind)
            | exact resolve b8e20 b8e219503
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e219503
          have b8e378704 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e8552 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e8552
            | (have j0 := b8e8552 (σ X0) X1
               grind)
            | exact resolve b8e8552 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8552
          have b8e378748 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e378704 X0 X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e378704
            | (have j0 := b8e378704 X0 X1
               grind)
            | exact resolve b8e378704 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e378704
          have b8e378754 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e378748 X0 X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e378748
            | (have j0 := b8e378748 X0 X1
               grind)
            | exact resolve b8e378748 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72 b8e378748
          have b8e378759 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e378754 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e378754
            | (have j0 := b8e378754 X0 X1
               grind)
            | exact resolve b8e378754 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e378754
          have b8e1198603 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e114648 y x
               grind)
            | exact superpose b8e114648 b8e20
            | (have j1 := b8e114648 y x
               grind)
            | exact resolve b8e20 b8e114648
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e114648
          have b8e1198616 : (σ (M.op x x)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
            first
            | (have j1 := b8e378759 x y
               grind)
            | (have r₁ := b8e1198603
               have r₂ := b8e378759 x y
               grind)
            | exact resolve b8e1198603 b8e378759
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e378759 b8e1198603
          have b8e1214594 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e1198616
               have i₂ := b8e165206
               grind)
            | exact superpose b8e165206 b8e1198616
            | exact resolve b8e1198616 b8e165206
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1214611 : (k y x) = (τ (σ (M.op x x))) ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b8e14 (k y x)
               have i₂ := b8e1198616
               grind)
            | exact superpose b8e1198616 b8e14
            | exact resolve b8e14 b8e1198616
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1198616
          have b8e1214634 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e1214594
          have b8e1214652 : (M.op x y) = (k y x) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b8e1214611
               have i₂ := b8e14 (M.op x x)
               grind)
            | exact superpose b8e14 b8e1214611
            | exact resolve b8e1214611 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1214611
          have b8e1230724 : (M.op x y) = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e1214652
               have i₂ := b8e165206
               grind)
            | exact superpose b8e165206 b8e1214652
            | exact resolve b8e1214652 b8e165206
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e165206
          have b8e1230738 : (M.op x y) ≠ (M.op x x) ∨ (M.op x x) = (k y x) := by grind
          clear b8e1214652
          have b8e1230747 : (M.op x y) = (M.op y y) ∨ (M.op y y) = (M.op x x) := by grind
          clear b8e1230724
          have b8e1230751 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b8e1230747
               have r₂ := b8e171963
               grind)
            | exact resolve b8e1230747 b8e171963
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e171963 b8e1230747
          have b8e1246879 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b8e226883
               have i₂ := b8e1230751
               grind)
            | exact superpose b8e1230751 b8e226883
            | exact resolve b8e226883 b8e1230751
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e226883
          have b8e1247118 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k y x) := by grind
          clear b8e1246879
          have b8e1247119 : (M.op x y) = (k y x) := by grind
          clear b8e1247118
          have b8e1253357 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e1999 x y
               have i₂ := b8e1247119
               grind)
            | exact superpose b8e1247119 b8e1999
            | (have j0 := b8e1999 x y
               grind)
            | exact resolve b8e1999 b8e1247119
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1999 b8e1247119
          have b8e1253381 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b8e1253357
               have r₂ := b8e20
               grind)
            | exact resolve b8e1253357 b8e20
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1253357
          have b8e1253387 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e1253381
               have i₂ := b8e1230751
               grind)
            | exact superpose b8e1230751 b8e1253381
            | exact resolve b8e1253381 b8e1230751
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1253381
          have b8e1253392 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
            first
            | (have r₁ := b8e1253387
               have r₂ := b8e20
               grind)
            | exact resolve b8e1253387 b8e20
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1253387
          have b8e1318752 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e171566
               have i₂ := b8e1214634
               grind)
            | exact superpose b8e1214634 b8e171566
            | exact resolve b8e171566 b8e1214634
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e171566 b8e1214634
          have b8e1318784 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) := by
            first
            | (have j1 := b8e17 y x
               grind)
            | (have r₁ := b8e1318752
               have r₂ := b8e17 y x
               grind)
            | exact resolve b8e1318752 b8e17
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1318752
          have b8e1318785 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x x) = (k y x) := by
            first
            | (have r₁ := b8e1318784
               have r₂ := b8e1230738
               grind)
            | exact resolve b8e1318784 b8e1230738
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1230738 b8e1318784
          have b8e1318786 : (M.op x x) = (k y x) := by
            first
            | (have r₁ := b8e1318785
               have r₂ := b8e1253392
               grind)
            | exact resolve b8e1318785 b8e1253392
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1318785
          have b8e1329582 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b8e2210 y x
               have i₂ := b8e1318786
               grind)
            | exact superpose b8e1318786 b8e2210
            | (have j0 := b8e2210 y x
               grind)
            | exact resolve b8e2210 b8e1318786
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2210 b8e1318786
          have b8e1329613 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
          clear b8e1329582
          have b8e1329629 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b8e1329613
               have i₂ := b8e1230751
               grind)
            | exact superpose b8e1230751 b8e1329613
            | exact resolve b8e1329613 b8e1230751
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1329613
          have b8e1329633 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b8e1329629
               have r₂ := b8e1253392
               grind)
            | exact resolve b8e1329629 b8e1253392
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1253392 b8e1329629
          have b8e1329634 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e1329633
               have i₂ := b8e1230751
               grind)
            | exact superpose b8e1230751 b8e1329633
            | exact resolve b8e1329633 b8e1230751
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1230751 b8e1329633
          have b8e1329635 : False := by grind
          exact b8e1329635

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op y y) := by grind
      have b0e20 : (σ x) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
           have i₂ := b0e11 X0 X1 X2
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e155 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e30 X0 x x X0
           have i₂ := b0e11 X0 x x
           grind)
        | exact superpose b0e11 b0e30
        | exact resolve b0e30 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30
      have b0e161 : (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e155 (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e155
        | exact resolve b0e155 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e162 : y = (M.op x y) := by
        first
        | (have i₁ := b0e155 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e155
        | exact resolve b0e155 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e155
      have b0e217 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e161
           grind)
        | exact superpose b0e161 b0e18
        | exact resolve b0e18 b0e161
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e161
      have b0e226 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e217
           have i₂ := b0e162
           grind)
        | exact superpose b0e162 b0e217
        | exact resolve b0e217 b0e162
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e162 b0e217
      have b0e227 : False := by grind
      exact b0e227
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op y y) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
             have i₂ := b1e12 X0 X1 X2
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e30 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e12 X0 (σ y) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e35 : (M.op y x) = (k x y) := by grind
        have b1e37 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e16 (σ x) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e16
          | (have j0 := b1e16 (σ x) (σ y)
             grind)
          | (have r₁ := b1e16 (σ x) (σ y)
             have r₂ := b1e22
             grind)
          | exact resolve b1e16 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e40 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b1e37
        have b1e41 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e40
             have r₂ := b1e21
             grind)
          | exact resolve b1e40 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40
        have b1e42 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e41
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e41
          | exact resolve b1e41 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41
        have b1e43 : (M.op (σ y) (σ y)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b1e42
             have i₂ := b1e35
             grind)
          | exact superpose b1e35 b1e42
          | exact resolve b1e42 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35 b1e42
        have b1e84 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) := by
          first
          | (have i₁ := b1e30 (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e30
          | exact resolve b1e30 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e90 : (σ x) = (M.op (σ (M.op y x)) (σ x)) := by
          first
          | (have i₁ := b1e84
             have i₂ := b1e43
             grind)
          | exact superpose b1e43 b1e84
          | exact resolve b1e84 b1e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e84
        have b1e156 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e28 X0 x x X0
             have i₂ := b1e12 X0 x x
             grind)
          | exact superpose b1e12 b1e28
          | exact resolve b1e28 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28
        have b1e166 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e30 (σ y)
             have i₂ := b1e156 (σ y)
             grind)
          | exact superpose b1e156 b1e30
          | exact resolve b1e30 b1e156
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30 b1e156
        have b1e220 : (σ y) = (σ (M.op y x)) := by
          first
          | (have i₁ := b1e43
             have i₂ := b1e166
             grind)
          | exact superpose b1e166 b1e43
          | exact resolve b1e43 b1e166
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43
        have b1e221 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e166
             grind)
          | exact superpose b1e166 b1e21
          | exact resolve b1e21 b1e166
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e166
        have b1e344 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b1e90
             have i₂ := b1e220
             grind)
          | exact superpose b1e220 b1e90
          | exact resolve b1e90 b1e220
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e90 b1e220
        have b1e361 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e344
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e344
          | exact resolve b1e344 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e344
        have b1e364 : False := by grind
        exact b1e364
      · have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op y y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e33 : (M.op y x) = (k x y) := by grind
        have b2e42 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e17 (σ X1) (σ X0)
             grind)
          | exact superpose b2e17 b2e18
          | (have j1 := b2e17 (σ X1) (σ X0)
             grind)
          | exact resolve b2e18 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e210 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e42 y y
             grind)
          | exact superpose b2e42 b2e21
          | (have j1 := b2e42 y y
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e42 y x
             grind)
          | exact resolve b2e21 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e244 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e42 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e42
        have b2e246 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e244 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e244
        have b2e251 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b2e210
        have b2e730 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e251
             have i₂ := b2e17 y y
             grind)
          | exact superpose b2e17 b2e251
          | (have j1 := b2e17 (σ y) (σ y)
             grind)
          | exact resolve b2e251 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e251
        have b2e731 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
        clear b2e730
        have b2e732 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e731
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e731
          | exact resolve b2e731 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e731
        have b2e733 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
        clear b2e732
        have b2e736 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
          first
          | (have i₁ := b2e733
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e733
          | exact resolve b2e733 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e733
        have b2e826 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ x = y := by grind
        clear b2e736
        have b2e843 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ x = y := by
          first
          | (have i₁ := b2e826
             have i₂ := b2e18 y y
             grind)
          | exact superpose b2e18 b2e826
          | exact resolve b2e826 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e826
        have b2e1824 : (σ x) ≠ (σ (k y y)) ∨ x = y := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e843
             grind)
          | exact superpose b2e843 b2e21
          | exact resolve b2e21 b2e843
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e843
        have b2e1998 : (σ x) ≠ (σ (M.op y y)) ∨ x = y ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e1824
             have i₂ := b2e17 y y
             grind)
          | exact superpose b2e17 b2e1824
          | (have j1 := b2e17 y y
             grind)
          | exact resolve b2e1824 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1824
        have b2e1999 : (σ x) ≠ (σ (M.op y y)) ∨ x = y ∨ y = (M.op y y) := by grind
        clear b2e1998
        have b2e2000 : (σ x) ≠ (σ x) ∨ x = y ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e1999
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1999
          | exact resolve b2e1999 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1999
        have b2e2001 : x = y ∨ y = (M.op y y) := by grind
        clear b2e2000
        have b2e2004 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e2001
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e2001
          | exact resolve b2e2001 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2001
        have b2e2005 : x = y := by grind
        clear b2e2004
        have b2e2201 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e2005
             grind)
          | exact superpose b2e2005 b2e22
          | exact resolve b2e22 b2e2005
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e2207 : (M.op y y) = (k y y) := by
          first
          | (have i₁ := b2e33
             have i₂ := b2e2005
             grind)
          | exact superpose b2e2005 b2e33
          | exact resolve b2e33 b2e2005
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33
        have b2e2242 : x = (k y y) := by
          first
          | (have i₁ := b2e2207
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e2207
          | exact resolve b2e2207 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2207
        have b2e2247 : y = (k y y) := by
          first
          | (have i₁ := b2e2242
             have i₂ := b2e2005
             grind)
          | exact superpose b2e2005 b2e2242
          | exact resolve b2e2242 b2e2005
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2005 b2e2242
        have b2e2755 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e246 y
             have i₂ := b2e2247
             grind)
          | exact superpose b2e2247 b2e246
          | (have j0 := b2e246 y
             grind)
          | exact resolve b2e246 b2e2247
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e246 b2e2247
        have b2e2760 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b2e2755
        have b2e2764 : False := by grind
        exact b2e2764
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
          intro X0 X1 X2
          grind
        have b3e20 : x ≠ (M.op y y) := by grind
        have b3e21 : y = (M.op y x) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e26 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) := by
          intro X0
          first
          | (have i₁ := b3e12 x y X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
             have i₂ := b3e12 X0 X1 X2
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e29 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
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
        have b3e32 : x = (M.op (M.op y y) x) := by
          first
          | (have i₁ := b3e26 x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e26
          | exact resolve b3e26 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26
        have b3e171 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b3e28 X0 x x X0
             have i₂ := b3e12 X0 x x
             grind)
          | exact superpose b3e12 b3e28
          | exact resolve b3e28 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28
        have b3e182 : y = (M.op y y) := by
          first
          | (have i₁ := b3e29 y
             have i₂ := b3e171 y
             grind)
          | exact superpose b3e171 b3e29
          | exact resolve b3e29 b3e171
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29 b3e171
        have b3e232 : x = (M.op y x) := by
          first
          | (have i₁ := b3e32
             have i₂ := b3e182
             grind)
          | exact superpose b3e182 b3e32
          | exact resolve b3e32 b3e182
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e233 : x ≠ y := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e182
             grind)
          | exact superpose b3e182 b3e20
          | exact resolve b3e20 b3e182
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e182
        have b3e245 : x = y := by
          first
          | (have i₁ := b3e232
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e232
          | exact resolve b3e232 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e232
        have b3e246 : False := by grind
        exact b3e246
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
            intro X0 X1 X2
            grind
          have b4e21 : x ≠ (M.op y y) := by grind
          have b4e22 : y = (M.op y x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e32 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) := by
            intro X0
            first
            | (have i₁ := b4e13 x y X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
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
          have b4e38 : x = (M.op (M.op y y) x) := by
            first
            | (have i₁ := b4e32 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e32
            | exact resolve b4e32 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e159 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e34 X0 x x X0
               have i₂ := b4e13 X0 x x
               grind)
            | exact superpose b4e13 b4e34
            | exact resolve b4e34 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e170 : y = (M.op y y) := by
            first
            | (have i₁ := b4e35 y
               have i₂ := b4e159 y
               grind)
            | exact superpose b4e159 b4e35
            | exact resolve b4e35 b4e159
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35 b4e159
          have b4e218 : x = (M.op y x) := by
            first
            | (have i₁ := b4e38
               have i₂ := b4e170
               grind)
            | exact superpose b4e170 b4e38
            | exact resolve b4e38 b4e170
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e219 : x ≠ y := by
            first
            | (have i₁ := b4e21
               have i₂ := b4e170
               grind)
            | exact superpose b4e170 b4e21
            | exact resolve b4e21 b4e170
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e170
          have b4e231 : x = y := by
            first
            | (have i₁ := b4e218
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e218
            | exact resolve b4e218 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e218
          have b4e232 : False := by grind
          exact b4e232
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
            intro X0 X1 X2
            grind
          have b5e21 : x ≠ (M.op y y) := by grind
          have b5e22 : y = (M.op y x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e32 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) := by
            intro X0
            first
            | (have i₁ := b5e13 x y X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e34 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
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
          have b5e36 : x = (M.op (M.op y y) x) := by
            first
            | (have i₁ := b5e32 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e32
            | exact resolve b5e32 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e120 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e33 X0 x x X0
               have i₂ := b5e13 X0 x x
               grind)
            | exact superpose b5e13 b5e33
            | exact resolve b5e33 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e128 : y = (M.op y y) := by
            first
            | (have i₁ := b5e34 y
               have i₂ := b5e120 y
               grind)
            | exact superpose b5e120 b5e34
            | exact resolve b5e34 b5e120
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e120
          have b5e164 : x = (M.op y x) := by
            first
            | (have i₁ := b5e36
               have i₂ := b5e128
               grind)
            | exact superpose b5e128 b5e36
            | exact resolve b5e36 b5e128
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36
          have b5e165 : x ≠ y := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e128
               grind)
            | exact superpose b5e128 b5e21
            | exact resolve b5e21 b5e128
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e128
          have b5e177 : x = y := by
            first
            | (have i₁ := b5e164
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e164
            | exact resolve b5e164 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e164
          have b5e178 : False := by grind
          exact b5e178
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : x ≠ (M.op y y) := by grind
        have b6e21 : y ≠ (M.op y x) := by grind
        have b6e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e27 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
             have i₂ := b6e12 X0 X1 X2
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e28 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ x)) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e12 X0 (σ y) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e34 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
        have b6e35 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e34
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e34
          | exact resolve b6e34 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e34
        have b6e54 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X1 X0
             have i₂ := b6e17 (σ X1) (σ X0)
             grind)
          | exact superpose b6e17 b6e18
          | (have j1 := b6e17 (σ X1) (σ X0)
             grind)
          | exact resolve b6e18 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e59 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e62 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e59 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e59
        have b6e139 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e27 X0 x x X0
             have i₂ := b6e12 X0 x x
             grind)
          | exact superpose b6e12 b6e27
          | exact resolve b6e27 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27
        have b6e144 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e139 (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e139
          | exact resolve b6e139 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e150 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X1 (M.op X0 X0) X0
             have i₂ := b6e139 X0
             grind)
          | exact superpose b6e139 b6e12
          | exact resolve b6e12 b6e139
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e139
        have b6e182 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e144
             grind)
          | exact superpose b6e144 b6e19
          | exact resolve b6e19 b6e144
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e144
        have b6e240 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e54 y y
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e54
          | exact resolve b6e54 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e54
        have b6e307 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
        clear b6e240
        have b6e376 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k y y)
             have i₂ := b6e307
             grind)
          | exact superpose b6e307 b6e13
          | exact resolve b6e13 b6e307
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e307
        have b6e389 : x = (k y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e376
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e376
          | exact resolve b6e376 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e376
        have b6e393 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e17 y y
             have i₂ := b6e389
             grind)
          | exact superpose b6e389 b6e17
          | (have j0 := b6e17 y y
             grind)
          | exact resolve b6e17 b6e389
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e389
        have b6e394 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by grind
        clear b6e393
        have b6e396 : y = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e394
             have r₂ := b6e20
             grind)
          | exact resolve b6e394 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e394
        have b6e479 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b6e150 (σ y) (σ x)
             have i₂ := b6e28 (σ y)
             grind)
          | exact superpose b6e28 b6e150
          | exact resolve b6e150 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28 b6e150
        have b6e524 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b6e35
             have i₂ := b6e479
             grind)
          | exact superpose b6e479 b6e35
          | exact resolve b6e35 b6e479
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35 b6e479
        have b6e579 : (k x y) = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e524
             grind)
          | exact superpose b6e524 b6e13
          | exact resolve b6e13 b6e524
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e524
        have b6e599 : x = (k x y) := by
          first
          | (have i₁ := b6e579
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e579
          | exact resolve b6e579 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e579
        have b6e648 : x = (M.op y x) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b6e62 x y
             have i₂ := b6e599
             grind)
          | exact superpose b6e599 b6e62
          | (have j0 := b6e62 x y
             grind)
          | exact resolve b6e62 b6e599
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e62 b6e599
        have b6e651 : x = (M.op y x) := by
          first
          | (have r₁ := b6e648
             have r₂ := b6e21
             grind)
          | exact resolve b6e648 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e648
        have b6e701 : x ≠ y := by
          first
          | (have i₁ := b6e21
             have i₂ := b6e651
             grind)
          | exact superpose b6e651 b6e21
          | exact resolve b6e21 b6e651
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e703 : ∀ X0 : G, (M.op (M.op (M.op y X0) x) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e12 X0 y x
             have i₂ := b6e651
             grind)
          | exact superpose b6e651 b6e12
          | exact resolve b6e12 b6e651
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e969 : y = (M.op (M.op y x) y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e703 y
             have i₂ := b6e396
             grind)
          | exact superpose b6e396 b6e703
          | exact resolve b6e703 b6e396
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e396 b6e703
        have b6e987 : y = (M.op x y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e969
             have i₂ := b6e651
             grind)
          | exact superpose b6e651 b6e969
          | exact resolve b6e969 b6e651
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e651 b6e969
        have b6e1064 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e182
             have i₂ := b6e987
             grind)
          | exact superpose b6e987 b6e182
          | exact resolve b6e182 b6e987
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e182 b6e987
        have b6e1077 : (σ x) = (σ y) := by grind
        clear b6e1064
        have b6e1153 : x = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 x
             have i₂ := b6e1077
             grind)
          | exact superpose b6e1077 b6e13
          | exact resolve b6e13 b6e1077
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1077
        have b6e1183 : x = y := by
          first
          | (have i₁ := b6e1153
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e1153
          | exact resolve b6e1153 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1153
        have b6e1193 : False := by grind
        exact b6e1193
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
            intro X0 X1 X2
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e34 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 := by
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
          have b7e54 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
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
          have b7e56 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b7e54
          have b7e57 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e56
               have r₂ := b7e23
               grind)
            | exact resolve b7e56 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e58 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e57
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e57
            | exact resolve b7e57 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e83 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) := by
            first
            | (have i₁ := b7e34 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e34
            | exact resolve b7e34 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e89 : (σ x) = (M.op (σ (k x y)) (σ x)) := by
            first
            | (have i₁ := b7e83
               have i₂ := b7e58
               grind)
            | exact superpose b7e58 b7e83
            | exact resolve b7e83 b7e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83
          have b7e143 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e33 X0 x x X0
               have i₂ := b7e13 X0 x x
               grind)
            | exact superpose b7e13 b7e33
            | exact resolve b7e33 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e152 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e34 (σ y)
               have i₂ := b7e143 (σ y)
               grind)
            | exact superpose b7e143 b7e34
            | exact resolve b7e34 b7e143
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34 b7e143
          have b7e190 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e58
               have i₂ := b7e152
               grind)
            | exact superpose b7e152 b7e58
            | exact resolve b7e58 b7e152
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58
          have b7e191 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e152
               grind)
            | exact superpose b7e152 b7e23
            | exact resolve b7e23 b7e152
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e152
          have b7e222 : (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b7e89
               have i₂ := b7e190
               grind)
            | exact superpose b7e190 b7e89
            | exact resolve b7e89 b7e190
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e89 b7e190
          have b7e234 : (σ x) = (σ y) := by
            first
            | (have i₁ := b7e222
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e222
            | exact resolve b7e222 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e222
          have b7e237 : False := by grind
          exact b7e237
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : y ≠ (M.op y x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e26 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 (τ X0) X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e19
            | exact resolve b8e19 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
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
          have b8e31 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e14 (k (τ X0) X1)
               have i₂ := b8e26 X0 X1
               grind)
            | exact superpose b8e26 b8e14
            | exact resolve b8e14 b8e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
               have i₂ := b8e13 X0 X1 X2
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e39 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e14 (k X0 (τ X1))
               have i₂ := b8e27 X1 X0
               grind)
            | exact superpose b8e27 b8e14
            | exact resolve b8e14 b8e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e42 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
            intro X0
            grind
          clear b8e27
          have b8e43 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e31 X1 (τ X0)
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e31
            | exact resolve b8e31 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e75 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e78 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e75 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e75
          have b8e95 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e78 (σ X1) (σ X0)
               grind)
            | exact superpose b8e78 b8e19
            | (have j1 := b8e78 (σ X1) (σ X0)
               grind)
            | exact resolve b8e19 b8e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e97 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X1 X0
               have i₂ := b8e78 (τ X1) X0
               grind)
            | exact superpose b8e78 b8e26
            | (have j1 := b8e78 (τ X1) X0
               grind)
            | exact resolve b8e26 b8e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e78
          have b8e106 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e32 X0 x x X0
               have i₂ := b8e13 X0 x x
               grind)
            | exact superpose b8e13 b8e32
            | exact resolve b8e32 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32
          have b8e132 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 (M.op X0 X0) X0
               have i₂ := b8e106 X0
               grind)
            | exact superpose b8e106 b8e13
            | exact resolve b8e13 b8e106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e106
          have b8e256 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e132 X0 (M.op X0 X1)
               have i₂ := b8e13 X0 X0 X1
               grind)
            | exact superpose b8e13 b8e132
            | exact resolve b8e132 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e132
          have b8e302 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 (M.op X0 X1) X0 X2
               have i₂ := b8e256 X0 X1
               grind)
            | exact superpose b8e256 b8e13
            | exact resolve b8e13 b8e256
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e560 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e97 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e97
            | exact resolve b8e97 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e607 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e560 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e560
            | (have j0 := b8e560 X0 X1
               grind)
            | exact resolve b8e560 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e560
          have b8e735 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
            intro X0
            first
            | (have i₁ := b8e42 X0
               have i₂ := b8e256 (τ X0) (τ X0)
               grind)
            | exact superpose b8e256 b8e42
            | exact resolve b8e42 b8e256
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e42
          have b8e873 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e95 x y
               grind)
            | exact superpose b8e95 b8e20
            | (have j1 := b8e95 x y
               grind)
            | exact resolve b8e20 b8e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e895 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e95 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e95
          have b8e1776 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e895 (τ X1) (τ X0)
               have i₂ := b8e43 X1 X0
               grind)
            | exact superpose b8e43 b8e895
            | (have j0 := b8e895 (τ X1) (τ X0)
               grind)
            | exact resolve b8e895 b8e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43
          have b8e1785 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e1776 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e1776
            | (have j0 := b8e1776 X0 X1
               grind)
            | exact resolve b8e1776 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1776
          have b8e1788 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e1785 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e1785
            | (have j0 := b8e1785 X0 X1
               grind)
            | exact resolve b8e1785 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1785
          have b8e1789 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e1788 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e1788
            | (have j0 := b8e1788 X0 X1
               grind)
            | exact resolve b8e1788 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1788
          have b8e1790 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e1789 X0 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e1789
            | (have j0 := b8e1789 X0 X1
               grind)
            | exact resolve b8e1789 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1789
          have b8e2999 : ∀ X0 : G, (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) = (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) := by
            intro X0
            first
            | (have i₁ := b8e31 (σ (M.op (τ (σ X0)) (τ (σ X0)))) X0
               have i₂ := b8e735 (σ X0)
               grind)
            | exact superpose b8e735 b8e31
            | exact resolve b8e31 b8e735
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e735
          have b8e3006 : ∀ X0 : G, (M.op (τ (σ X0)) (τ (σ X0))) = (k (M.op (τ (σ X0)) (τ (σ X0))) X0) := by
            intro X0
            first
            | (have i₁ := b8e2999 X0
               have i₂ := b8e14 (M.op (τ (σ X0)) (τ (σ X0)))
               grind)
            | exact superpose b8e14 b8e2999
            | exact resolve b8e2999 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2999
          have b8e3031 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have i₁ := b8e3006 X0
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e3006
            | exact resolve b8e3006 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3006
          have b8e3225 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
            intro X0
            first
            | (have i₁ := b8e31 (M.op (σ X0) (σ X0)) X0
               have i₂ := b8e3031 (σ X0)
               grind)
            | exact superpose b8e3031 b8e31
            | exact resolve b8e31 b8e3031
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31
          have b8e4372 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e873
               have i₂ := b8e607 y x
               grind)
            | exact superpose b8e607 b8e873
            | (have j1 := b8e607 (σ y) (σ x)
               grind)
            | (have r₁ := b8e873
               have r₂ := b8e607 y x
               grind)
            | exact resolve b8e873 b8e607
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e607
          have b8e4373 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
          clear b8e4372
          have b8e4552 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e256 (σ x) (σ y)
               have i₂ := b8e4373
               grind)
            | exact superpose b8e4373 b8e256
            | exact resolve b8e256 b8e4373
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4373
          have b8e5174 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e3225 x
               have i₂ := b8e4552
               grind)
            | exact superpose b8e4552 b8e3225
            | exact resolve b8e3225 b8e4552
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3225 b8e4552
          have b8e5249 : x = (k x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e5174
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e5174
            | exact resolve b8e5174 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5174
          have b8e5410 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e1790 x x
               have i₂ := b8e5249
               grind)
            | exact superpose b8e5249 b8e1790
            | (have j0 := b8e1790 x x
               grind)
            | (have r₁ := b8e1790 x x
               have r₂ := b8e5249
               grind)
            | exact resolve b8e1790 b8e5249
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1790 b8e5249
          have b8e5414 : x = (M.op x x) ∨ x = (M.op x y) := by grind
          clear b8e5410
          have b8e5781 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e13 X0 x x
               have i₂ := b8e5414
               grind)
            | exact superpose b8e5414 b8e13
            | exact resolve b8e13 b8e5414
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e5819 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e302 x x x
               have i₂ := b8e5414
               grind)
            | exact superpose b8e5414 b8e302
            | exact resolve b8e302 b8e5414
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5414
          have b8e5822 : ∀ X0 : G, x = (M.op (M.op x X0) x) ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e5819 X0
               have i₂ := b8e256 x X0
               grind)
            | exact superpose b8e256 b8e5819
            | exact resolve b8e5819 b8e256
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5819
          have b8e7489 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e5781 X0
               have i₂ := b8e5822 X0
               grind)
            | exact superpose b8e5822 b8e5781
            | exact resolve b8e5781 b8e5822
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5781 b8e5822
          have b8e7565 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (M.op x y) := by
            intro X0
            first
            | (have j0 := b8e7489 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7489
          have b8e7879 : ∀ X0 : G, x = (M.op x x) ∨ (M.op x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e256 x y
               have i₂ := b8e7565 X0
               grind)
            | exact superpose b8e7565 b8e256
            | (have j1 := b8e7565 x
               grind)
            | exact resolve b8e256 b8e7565
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7565
          have b8e8338 : x ≠ x ∨ x = (M.op x x) := by
            first
            | (have j0 := b8e7879 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7879
          have b8e8339 : x = (M.op x x) := by grind
          clear b8e8338
          have b8e8518 : x = (k x x) := by
            first
            | (have i₁ := b8e3031 x
               have i₂ := b8e8339
               grind)
            | exact superpose b8e8339 b8e3031
            | exact resolve b8e3031 b8e8339
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3031
          have b8e8520 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e13 X0 x x
               have i₂ := b8e8339
               grind)
            | exact superpose b8e8339 b8e13
            | exact resolve b8e13 b8e8339
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e8570 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
            intro X0
            first
            | (have i₁ := b8e302 x x x
               have i₂ := b8e8339
               grind)
            | exact superpose b8e8339 b8e302
            | exact resolve b8e302 b8e8339
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e302 b8e8339
          have b8e8573 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
            intro X0
            first
            | (have i₁ := b8e8570 X0
               have i₂ := b8e256 x X0
               grind)
            | exact superpose b8e256 b8e8570
            | exact resolve b8e8570 b8e256
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e256 b8e8570
          have b8e8894 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e895 x x
               have i₂ := b8e8518
               grind)
            | exact superpose b8e8518 b8e895
            | (have j0 := b8e895 x x
               grind)
            | exact resolve b8e895 b8e8518
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e895 b8e8518
          have b8e8900 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b8e8894
          have b8e10607 : ∀ X0 : G, (M.op x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e8520 X0
               have i₂ := b8e8573 X0
               grind)
            | exact superpose b8e8573 b8e8520
            | exact resolve b8e8520 b8e8573
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e10685 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op x (τ X0)) x))) ∨ (τ X0) = (M.op (M.op x (τ X0)) x) := by
            intro X0
            first
            | (have i₁ := b8e97 (M.op (M.op x (τ x)) x) x
               have i₂ := b8e8520 (τ x)
               grind)
            | exact superpose b8e8520 b8e97
            | exact resolve b8e97 b8e8520
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e97 b8e8520
          have b8e10686 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) ∨ (τ X0) = (M.op (M.op x (τ X0)) x) := by
            intro X0
            first
            | (have i₁ := b8e10685 X0
               have i₂ := b8e8573 (τ X0)
               grind)
            | exact superpose b8e8573 b8e10685
            | (have j0 := b8e10685 X0
               grind)
            | exact resolve b8e10685 b8e8573
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10685
          have b8e10719 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (τ X0) = (M.op (M.op x (τ X0)) x) := by
            intro X0
            first
            | (have i₁ := b8e10686 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e10686
            | (have j0 := b8e10686 X0
               grind)
            | exact resolve b8e10686 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10686
          have b8e10746 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (τ X0) = x := by
            intro X0
            first
            | (have i₁ := b8e10719 X0
               have i₂ := b8e8573 (τ X0)
               grind)
            | exact superpose b8e8573 b8e10719
            | (have j0 := b8e10719 X0
               grind)
            | exact resolve b8e10719 b8e8573
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10719
          have b8e11068 : ∀ X0 : G, x = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b8e8573 X0
               have i₂ := b8e10607 X0
               grind)
            | exact superpose b8e10607 b8e8573
            | exact resolve b8e8573 b8e10607
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8573
          have b8e11703 : x ≠ y := by
            first
            | (have i₁ := b8e22
               have i₂ := b8e11068 y
               grind)
            | exact superpose b8e11068 b8e22
            | exact resolve b8e22 b8e11068
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11068
          have b8e15205 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ x))) ∨ (τ (σ X0)) = x := by
            intro X0
            first
            | (have i₁ := b8e39 X0 (σ x)
               have i₂ := b8e10746 (σ X0)
               grind)
            | exact superpose b8e10746 b8e39
            | (have j1 := b8e10746 (σ X0)
               grind)
            | exact resolve b8e39 b8e10746
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e39 b8e10746
          have b8e15268 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) ∨ (τ (σ X0)) = x := by
            intro X0
            first
            | (have i₁ := b8e15205 X0
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e15205
            | (have j0 := b8e15205 X0
               grind)
            | exact resolve b8e15205 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15205
          have b8e15300 : ∀ X0 : G, (k X0 x) = X0 ∨ (τ (σ X0)) = x := by
            intro X0
            first
            | (have i₁ := b8e15268 X0
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e15268
            | (have j0 := b8e15268 X0
               grind)
            | exact resolve b8e15268 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15268
          have b8e15311 : ∀ X0 : G, (k X0 x) = X0 ∨ x = X0 := by
            intro X0
            first
            | (have i₁ := b8e15300 X0
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e15300
            | (have j0 := b8e15300 X0
               grind)
            | exact resolve b8e15300 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15300
          have b8e15402 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
            first
            | (have i₁ := b8e873
               have i₂ := b8e15311 y
               grind)
            | exact superpose b8e15311 b8e873
            | (have j1 := b8e15311 y
               grind)
            | exact resolve b8e873 b8e15311
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e873
          have b8e15403 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e15402
               have r₂ := b8e11703
               grind)
            | exact resolve b8e15402 b8e11703
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15402
          have b8e15432 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e15403
               have i₂ := b8e10607 y
               grind)
            | exact superpose b8e10607 b8e15403
            | exact resolve b8e15403 b8e10607
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15403
          have b8e15433 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b8e15432
          have b8e15455 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e15433
               grind)
            | exact superpose b8e15433 b8e20
            | exact resolve b8e20 b8e15433
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e15466 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e15433
               grind)
            | exact superpose b8e15433 b8e17
            | (have j0 := b8e17 (σ y) (σ x)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e15433
               grind)
            | exact resolve b8e17 b8e15433
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15433
          have b8e15520 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by grind
          clear b8e15466
          have b8e15528 : (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b8e15520
               have i₂ := b8e8900
               grind)
            | exact superpose b8e8900 b8e15520
            | exact resolve b8e15520 b8e8900
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15520
          have b8e15536 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b8e15455
               have i₂ := b8e10607 y
               grind)
            | exact superpose b8e10607 b8e15455
            | exact resolve b8e15455 b8e10607
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10607 b8e15455
          have b8e15541 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e15528
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e15528
            | exact resolve b8e15528 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15528
          have b8e15545 : (σ (k y x)) = (M.op (σ x) (σ x)) := by
            first
            | (have r₁ := b8e15541
               have r₂ := b8e15536
               grind)
            | exact resolve b8e15541 b8e15536
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15541
          have b8e15546 : (σ x) = (σ (k y x)) := by
            first
            | (have i₁ := b8e15545
               have i₂ := b8e8900
               grind)
            | exact superpose b8e8900 b8e15545
            | exact resolve b8e15545 b8e8900
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8900 b8e15545
          have b8e16056 : (σ x) = (σ y) ∨ x = y := by
            first
            | (have i₁ := b8e15546
               have i₂ := b8e15311 y
               grind)
            | exact superpose b8e15311 b8e15546
            | (have j1 := b8e15311 y
               grind)
            | exact resolve b8e15546 b8e15311
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15311 b8e15546
          have b8e16156 : x = y := by
            first
            | (have r₁ := b8e16056
               have r₂ := b8e15536
               grind)
            | exact resolve b8e16056 b8e15536
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15536 b8e16056
          have b8e16165 : False := by grind
          exact b8e16165

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_y_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op y y) := by grind
      have b0e20 : (σ x) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
           have i₂ := b0e11 X0 X1 X2
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e155 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e30 X0 x x X0
           have i₂ := b0e11 X0 x x
           grind)
        | exact superpose b0e11 b0e30
        | exact resolve b0e30 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30
      have b0e161 : (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e155 (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e155
        | exact resolve b0e155 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e162 : y = (M.op x y) := by
        first
        | (have i₁ := b0e155 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e155
        | exact resolve b0e155 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e155
      have b0e217 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e161
           grind)
        | exact superpose b0e161 b0e18
        | exact resolve b0e18 b0e161
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e161
      have b0e226 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e217
           have i₂ := b0e162
           grind)
        | exact superpose b0e162 b0e217
        | exact resolve b0e217 b0e162
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e162 b0e217
      have b0e227 : False := by grind
      exact b0e227
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op y y) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e29 : ∀ X0 : G, (M.op (M.op (M.op y X0) x) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e12 X0 y y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e35 : (M.op y x) = (k x y) := by grind
        have b1e37 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e16 (σ x) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e16
          | (have j0 := b1e16 (σ x) (σ y)
             grind)
          | (have r₁ := b1e16 (σ x) (σ y)
             have r₂ := b1e22
             grind)
          | exact resolve b1e16 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e40 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e37
        have b1e41 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e40
             have r₂ := b1e21
             grind)
          | exact resolve b1e40 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40
        have b1e42 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e41
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e41
          | exact resolve b1e41 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41
        have b1e43 : (σ y) = (σ (M.op y x)) := by
          first
          | (have i₁ := b1e42
             have i₂ := b1e35
             grind)
          | exact superpose b1e35 b1e42
          | exact resolve b1e42 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35 b1e42
        have b1e46 : (M.op y x) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (M.op y x)
             have i₂ := b1e43
             grind)
          | exact superpose b1e43 b1e13
          | exact resolve b1e13 b1e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43
        have b1e47 : y = (M.op y x) := by
          first
          | (have i₁ := b1e46
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e46
          | exact resolve b1e46 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46
        have b1e66 : x = (M.op (M.op y x) x) := by
          first
          | (have i₁ := b1e29 x
             have i₂ := b1e47
             grind)
          | exact superpose b1e47 b1e29
          | exact resolve b1e29 b1e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29
        have b1e70 : x = (M.op y x) := by
          first
          | (have i₁ := b1e66
             have i₂ := b1e47
             grind)
          | exact superpose b1e47 b1e66
          | exact resolve b1e66 b1e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e66
        have b1e71 : x = y := by
          first
          | (have i₁ := b1e70
             have i₂ := b1e47
             grind)
          | exact superpose b1e47 b1e70
          | exact resolve b1e70 b1e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47 b1e70
        have b1e73 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e71
             grind)
          | exact superpose b1e71 b1e22
          | exact resolve b1e22 b1e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e174 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e73
             grind)
          | exact superpose b1e73 b1e21
          | exact resolve b1e21 b1e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e73
        have b1e184 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e174
             have i₂ := b1e71
             grind)
          | exact superpose b1e71 b1e174
          | exact resolve b1e174 b1e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e71 b1e174
        have b1e185 : False := by grind
        exact b1e185
      · have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op y y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e33 : (M.op y x) = (k x y) := by grind
        have b2e42 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e17 (σ X1) (σ X0)
             grind)
          | exact superpose b2e17 b2e18
          | (have j1 := b2e17 (σ X1) (σ X0)
             grind)
          | exact resolve b2e18 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e210 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e42 y y
             grind)
          | exact superpose b2e42 b2e21
          | (have j1 := b2e42 y y
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e42 y x
             grind)
          | exact resolve b2e21 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e244 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e42 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e42
        have b2e246 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e244 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e244
        have b2e251 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b2e210
        have b2e729 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e251
             have i₂ := b2e17 y y
             grind)
          | exact superpose b2e17 b2e251
          | (have j1 := b2e17 (σ y) (σ y)
             grind)
          | exact resolve b2e251 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e251
        have b2e730 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
        clear b2e729
        have b2e731 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e730
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e730
          | exact resolve b2e730 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e730
        have b2e732 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
        clear b2e731
        have b2e735 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
          first
          | (have i₁ := b2e732
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e732
          | exact resolve b2e732 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e732
        have b2e825 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ x = y := by grind
        clear b2e735
        have b2e842 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ x = y := by
          first
          | (have i₁ := b2e825
             have i₂ := b2e18 y y
             grind)
          | exact superpose b2e18 b2e825
          | exact resolve b2e825 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e825
        have b2e1966 : (σ x) ≠ (σ (k y y)) ∨ x = y := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e842
             grind)
          | exact superpose b2e842 b2e21
          | exact resolve b2e21 b2e842
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e842
        have b2e2145 : (σ x) ≠ (σ (M.op y y)) ∨ x = y ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e1966
             have i₂ := b2e17 y y
             grind)
          | exact superpose b2e17 b2e1966
          | (have j1 := b2e17 y y
             grind)
          | exact resolve b2e1966 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1966
        have b2e2146 : (σ x) ≠ (σ (M.op y y)) ∨ x = y ∨ y = (M.op y y) := by grind
        clear b2e2145
        have b2e2147 : (σ x) ≠ (σ x) ∨ x = y ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e2146
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e2146
          | exact resolve b2e2146 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2146
        have b2e2148 : x = y ∨ y = (M.op y y) := by grind
        clear b2e2147
        have b2e2151 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e2148
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e2148
          | exact resolve b2e2148 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2148
        have b2e2152 : x = y := by grind
        clear b2e2151
        have b2e2387 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e2152
             grind)
          | exact superpose b2e2152 b2e22
          | exact resolve b2e22 b2e2152
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e2393 : (M.op y y) = (k y y) := by
          first
          | (have i₁ := b2e33
             have i₂ := b2e2152
             grind)
          | exact superpose b2e2152 b2e33
          | exact resolve b2e33 b2e2152
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33
        have b2e2430 : x = (k y y) := by
          first
          | (have i₁ := b2e2393
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e2393
          | exact resolve b2e2393 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2393
        have b2e2435 : y = (k y y) := by
          first
          | (have i₁ := b2e2430
             have i₂ := b2e2152
             grind)
          | exact superpose b2e2152 b2e2430
          | exact resolve b2e2430 b2e2152
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2152 b2e2430
        have b2e2868 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e246 y
             have i₂ := b2e2435
             grind)
          | exact superpose b2e2435 b2e246
          | (have j0 := b2e246 y
             grind)
          | exact resolve b2e246 b2e2435
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e246 b2e2435
        have b2e2873 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b2e2868
        have b2e2877 : False := by grind
        exact b2e2877
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : x ≠ (M.op y y) := by grind
        have b3e21 : y = (M.op y x) := by grind
        have b3e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e30 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ x)) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b3e12 X0 (σ y) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e35 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
        have b3e36 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e35
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e35
          | exact resolve b3e35 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e35
        have b3e39 : y ≠ y ∨ x = (M.op y y) ∨ y = (k x y) := by
          first
          | (have i₁ := b3e16 x y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e16
          | (have j0 := b3e16 x y
             grind)
          | (have r₁ := b3e16 x y
             have r₂ := b3e21
             grind)
          | exact resolve b3e16 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e44 : x = (M.op y y) ∨ y = (k x y) := by grind
        clear b3e39
        have b3e45 : y = (k x y) := by
          first
          | (have r₁ := b3e44
             have r₂ := b3e20
             grind)
          | exact resolve b3e44 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44
        have b3e96 : (σ x) = (M.op (M.op (σ (k x y)) (σ x)) (σ x)) := by
          first
          | (have i₁ := b3e30 (σ x)
             have i₂ := b3e36
             grind)
          | exact superpose b3e36 b3e30
          | exact resolve b3e30 b3e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30
        have b3e101 : (σ x) = (M.op (M.op (σ y) (σ x)) (σ x)) := by
          first
          | (have i₁ := b3e96
             have i₂ := b3e45
             grind)
          | exact superpose b3e45 b3e96
          | exact resolve b3e96 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e96
        have b3e102 : (σ x) = (M.op (σ (k x y)) (σ x)) := by
          first
          | (have i₁ := b3e101
             have i₂ := b3e36
             grind)
          | exact superpose b3e36 b3e101
          | exact resolve b3e101 b3e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e101
        have b3e103 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b3e102
             have i₂ := b3e45
             grind)
          | exact superpose b3e45 b3e102
          | exact resolve b3e102 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e102
        have b3e105 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b3e36
             have i₂ := b3e103
             grind)
          | exact superpose b3e103 b3e36
          | exact resolve b3e36 b3e103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e36
        have b3e110 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e105
             have i₂ := b3e45
             grind)
          | exact superpose b3e45 b3e105
          | exact resolve b3e105 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45 b3e105
        have b3e121 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e103
             have i₂ := b3e110
             grind)
          | exact superpose b3e110 b3e103
          | exact resolve b3e103 b3e110
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e103
        have b3e128 : x = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 x
             have i₂ := b3e110
             grind)
          | exact superpose b3e110 b3e13
          | exact resolve b3e13 b3e110
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e110
        have b3e129 : x = y := by
          first
          | (have i₁ := b3e128
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e128
          | exact resolve b3e128 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e128
        have b3e154 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e129
             grind)
          | exact superpose b3e129 b3e19
          | exact resolve b3e19 b3e129
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e155 : y = (M.op y y) := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e129
             grind)
          | exact superpose b3e129 b3e21
          | exact resolve b3e21 b3e129
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e129
        have b3e164 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e154
             have i₂ := b3e155
             grind)
          | exact superpose b3e155 b3e154
          | exact resolve b3e154 b3e155
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e154 b3e155
        have b3e165 : False := by grind
        exact b3e165
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
            intro X0 X1 X2
            grind
          have b4e21 : x ≠ (M.op y y) := by grind
          have b4e22 : y = (M.op y x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e32 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) := by
            intro X0
            first
            | (have i₁ := b4e13 x y X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
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
          have b4e38 : x = (M.op (M.op y y) x) := by
            first
            | (have i₁ := b4e32 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e32
            | exact resolve b4e32 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e166 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e34 X0 x x X0
               have i₂ := b4e13 X0 x x
               grind)
            | exact superpose b4e13 b4e34
            | exact resolve b4e34 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e176 : y = (M.op y y) := by
            first
            | (have i₁ := b4e35 y
               have i₂ := b4e166 y
               grind)
            | exact superpose b4e166 b4e35
            | exact resolve b4e35 b4e166
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35 b4e166
          have b4e222 : x = (M.op y x) := by
            first
            | (have i₁ := b4e38
               have i₂ := b4e176
               grind)
            | exact superpose b4e176 b4e38
            | exact resolve b4e38 b4e176
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e223 : x ≠ y := by
            first
            | (have i₁ := b4e21
               have i₂ := b4e176
               grind)
            | exact superpose b4e176 b4e21
            | exact resolve b4e21 b4e176
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e176
          have b4e235 : x = y := by
            first
            | (have i₁ := b4e222
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e222
            | exact resolve b4e222 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e222
          have b4e236 : False := by grind
          exact b4e236
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
            intro X0 X1 X2
            grind
          have b5e21 : x ≠ (M.op y y) := by grind
          have b5e22 : y = (M.op y x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e32 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) := by
            intro X0
            first
            | (have i₁ := b5e13 x y X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e34 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
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
          have b5e36 : x = (M.op (M.op y y) x) := by
            first
            | (have i₁ := b5e32 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e32
            | exact resolve b5e32 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e124 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e33 X0 x x X0
               have i₂ := b5e13 X0 x x
               grind)
            | exact superpose b5e13 b5e33
            | exact resolve b5e33 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e132 : y = (M.op y y) := by
            first
            | (have i₁ := b5e34 y
               have i₂ := b5e124 y
               grind)
            | exact superpose b5e124 b5e34
            | exact resolve b5e34 b5e124
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e124
          have b5e168 : x = (M.op y x) := by
            first
            | (have i₁ := b5e36
               have i₂ := b5e132
               grind)
            | exact superpose b5e132 b5e36
            | exact resolve b5e36 b5e132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36
          have b5e169 : x ≠ y := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e132
               grind)
            | exact superpose b5e132 b5e21
            | exact resolve b5e21 b5e132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e132
          have b5e181 : x = y := by
            first
            | (have i₁ := b5e168
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e168
            | exact resolve b5e168 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e168
          have b5e182 : False := by grind
          exact b5e182
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : x ≠ (M.op y y) := by grind
        have b6e21 : y ≠ (M.op y x) := by grind
        have b6e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e27 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
             have i₂ := b6e12 X0 X1 X2
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e28 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ x)) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e12 X0 (σ y) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e34 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
        have b6e35 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e34
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e34
          | exact resolve b6e34 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e34
        have b6e54 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X1 X0
             have i₂ := b6e17 (σ X1) (σ X0)
             grind)
          | exact superpose b6e17 b6e18
          | (have j1 := b6e17 (σ X1) (σ X0)
             grind)
          | exact resolve b6e18 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e59 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e62 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e59 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e59
        have b6e139 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e27 X0 x x X0
             have i₂ := b6e12 X0 x x
             grind)
          | exact superpose b6e12 b6e27
          | exact resolve b6e27 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27
        have b6e144 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e139 (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e139
          | exact resolve b6e139 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e150 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X1 (M.op X0 X0) X0
             have i₂ := b6e139 X0
             grind)
          | exact superpose b6e139 b6e12
          | exact resolve b6e12 b6e139
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e139
        have b6e182 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e144
             grind)
          | exact superpose b6e144 b6e19
          | exact resolve b6e19 b6e144
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e144
        have b6e240 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e54 y y
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e54
          | exact resolve b6e54 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e54
        have b6e307 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
        clear b6e240
        have b6e376 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k y y)
             have i₂ := b6e307
             grind)
          | exact superpose b6e307 b6e13
          | exact resolve b6e13 b6e307
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e307
        have b6e389 : x = (k y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e376
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e376
          | exact resolve b6e376 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e376
        have b6e393 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e17 y y
             have i₂ := b6e389
             grind)
          | exact superpose b6e389 b6e17
          | (have j0 := b6e17 y y
             grind)
          | exact resolve b6e17 b6e389
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e389
        have b6e394 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by grind
        clear b6e393
        have b6e396 : y = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e394
             have r₂ := b6e20
             grind)
          | exact resolve b6e394 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e394
        have b6e479 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b6e150 (σ y) (σ x)
             have i₂ := b6e28 (σ y)
             grind)
          | exact superpose b6e28 b6e150
          | exact resolve b6e150 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28 b6e150
        have b6e524 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b6e35
             have i₂ := b6e479
             grind)
          | exact superpose b6e479 b6e35
          | exact resolve b6e35 b6e479
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35 b6e479
        have b6e579 : (k x y) = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e524
             grind)
          | exact superpose b6e524 b6e13
          | exact resolve b6e13 b6e524
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e524
        have b6e599 : x = (k x y) := by
          first
          | (have i₁ := b6e579
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e579
          | exact resolve b6e579 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e579
        have b6e648 : x = (M.op y x) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b6e62 x y
             have i₂ := b6e599
             grind)
          | exact superpose b6e599 b6e62
          | (have j0 := b6e62 x y
             grind)
          | exact resolve b6e62 b6e599
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e62 b6e599
        have b6e651 : x = (M.op y x) := by
          first
          | (have r₁ := b6e648
             have r₂ := b6e21
             grind)
          | exact resolve b6e648 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e648
        have b6e701 : x ≠ y := by
          first
          | (have i₁ := b6e21
             have i₂ := b6e651
             grind)
          | exact superpose b6e651 b6e21
          | exact resolve b6e21 b6e651
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e703 : ∀ X0 : G, (M.op (M.op (M.op y X0) x) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e12 X0 y x
             have i₂ := b6e651
             grind)
          | exact superpose b6e651 b6e12
          | exact resolve b6e12 b6e651
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e969 : y = (M.op (M.op y x) y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e703 y
             have i₂ := b6e396
             grind)
          | exact superpose b6e396 b6e703
          | exact resolve b6e703 b6e396
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e396 b6e703
        have b6e987 : y = (M.op x y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e969
             have i₂ := b6e651
             grind)
          | exact superpose b6e651 b6e969
          | exact resolve b6e969 b6e651
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e651 b6e969
        have b6e1064 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e182
             have i₂ := b6e987
             grind)
          | exact superpose b6e987 b6e182
          | exact resolve b6e182 b6e987
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e182 b6e987
        have b6e1077 : (σ x) = (σ y) := by grind
        clear b6e1064
        have b6e1153 : x = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 x
             have i₂ := b6e1077
             grind)
          | exact superpose b6e1077 b6e13
          | exact resolve b6e13 b6e1077
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1077
        have b6e1183 : x = y := by
          first
          | (have i₁ := b6e1153
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e1153
          | exact resolve b6e1153 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1153
        have b6e1193 : False := by grind
        exact b6e1193
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ (M.op y y) := by grind
          have b7e22 : y ≠ (M.op y x) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e54 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e56 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e54
          have b7e57 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e56
               have r₂ := b7e23
               grind)
            | exact resolve b7e56 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e58 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e57
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e57
            | exact resolve b7e57 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e62 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e58
               grind)
            | exact superpose b7e58 b7e14
            | exact resolve b7e14 b7e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58
          have b7e63 : y = (k x y) := by
            first
            | (have i₁ := b7e62
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e62
            | exact resolve b7e62 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e84 : y = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e63
               grind)
            | exact superpose b7e63 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63
          have b7e85 : y = (M.op y x) ∨ x = (M.op y y) := by grind
          clear b7e84
          have b7e87 : x = (M.op y y) := by
            first
            | (have r₁ := b7e85
               have r₂ := b7e22
               grind)
            | exact resolve b7e85 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e85
          have b7e89 : False := by grind
          exact b7e89
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : y ≠ (M.op y x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e26 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 (τ X0) X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e19
            | exact resolve b8e19 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
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
          have b8e31 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e14 (k (τ X0) X1)
               have i₂ := b8e26 X0 X1
               grind)
            | exact superpose b8e26 b8e14
            | exact resolve b8e14 b8e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
               have i₂ := b8e13 X0 X1 X2
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e39 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e14 (k X0 (τ X1))
               have i₂ := b8e27 X1 X0
               grind)
            | exact superpose b8e27 b8e14
            | exact resolve b8e14 b8e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e42 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
            intro X0
            grind
          clear b8e27
          have b8e43 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e31 X1 (τ X0)
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e31
            | exact resolve b8e31 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e75 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e78 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e75 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e75
          have b8e95 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e78 (σ X1) (σ X0)
               grind)
            | exact superpose b8e78 b8e19
            | (have j1 := b8e78 (σ X1) (σ X0)
               grind)
            | exact resolve b8e19 b8e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e97 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X1 X0
               have i₂ := b8e78 (τ X1) X0
               grind)
            | exact superpose b8e78 b8e26
            | (have j1 := b8e78 (τ X1) X0
               grind)
            | exact resolve b8e26 b8e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e78
          have b8e106 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e32 X0 x x X0
               have i₂ := b8e13 X0 x x
               grind)
            | exact superpose b8e13 b8e32
            | exact resolve b8e32 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32
          have b8e132 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 (M.op X0 X0) X0
               have i₂ := b8e106 X0
               grind)
            | exact superpose b8e106 b8e13
            | exact resolve b8e13 b8e106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e106
          have b8e256 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e132 X0 (M.op X0 X1)
               have i₂ := b8e13 X0 X0 X1
               grind)
            | exact superpose b8e13 b8e132
            | exact resolve b8e132 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e132
          have b8e302 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 (M.op X0 X1) X0 X2
               have i₂ := b8e256 X0 X1
               grind)
            | exact superpose b8e256 b8e13
            | exact resolve b8e13 b8e256
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e560 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e97 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e97
            | exact resolve b8e97 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e607 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e560 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e560
            | (have j0 := b8e560 X0 X1
               grind)
            | exact resolve b8e560 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e560
          have b8e735 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
            intro X0
            first
            | (have i₁ := b8e42 X0
               have i₂ := b8e256 (τ X0) (τ X0)
               grind)
            | exact superpose b8e256 b8e42
            | exact resolve b8e42 b8e256
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e42
          have b8e873 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e95 x y
               grind)
            | exact superpose b8e95 b8e20
            | (have j1 := b8e95 x y
               grind)
            | exact resolve b8e20 b8e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e895 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e95 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e95
          have b8e1776 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e895 (τ X1) (τ X0)
               have i₂ := b8e43 X1 X0
               grind)
            | exact superpose b8e43 b8e895
            | (have j0 := b8e895 (τ X1) (τ X0)
               grind)
            | exact resolve b8e895 b8e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43
          have b8e1785 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e1776 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e1776
            | (have j0 := b8e1776 X0 X1
               grind)
            | exact resolve b8e1776 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1776
          have b8e1788 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e1785 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e1785
            | (have j0 := b8e1785 X0 X1
               grind)
            | exact resolve b8e1785 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1785
          have b8e1789 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e1788 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e1788
            | (have j0 := b8e1788 X0 X1
               grind)
            | exact resolve b8e1788 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1788
          have b8e1790 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e1789 X0 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e1789
            | (have j0 := b8e1789 X0 X1
               grind)
            | exact resolve b8e1789 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1789
          have b8e2999 : ∀ X0 : G, (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) = (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) := by
            intro X0
            first
            | (have i₁ := b8e31 (σ (M.op (τ (σ X0)) (τ (σ X0)))) X0
               have i₂ := b8e735 (σ X0)
               grind)
            | exact superpose b8e735 b8e31
            | exact resolve b8e31 b8e735
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e735
          have b8e3006 : ∀ X0 : G, (M.op (τ (σ X0)) (τ (σ X0))) = (k (M.op (τ (σ X0)) (τ (σ X0))) X0) := by
            intro X0
            first
            | (have i₁ := b8e2999 X0
               have i₂ := b8e14 (M.op (τ (σ X0)) (τ (σ X0)))
               grind)
            | exact superpose b8e14 b8e2999
            | exact resolve b8e2999 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2999
          have b8e3031 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have i₁ := b8e3006 X0
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e3006
            | exact resolve b8e3006 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3006
          have b8e3225 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
            intro X0
            first
            | (have i₁ := b8e31 (M.op (σ X0) (σ X0)) X0
               have i₂ := b8e3031 (σ X0)
               grind)
            | exact superpose b8e3031 b8e31
            | exact resolve b8e31 b8e3031
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31
          have b8e4372 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e873
               have i₂ := b8e607 y x
               grind)
            | exact superpose b8e607 b8e873
            | (have j1 := b8e607 (σ y) (σ x)
               grind)
            | (have r₁ := b8e873
               have r₂ := b8e607 y x
               grind)
            | exact resolve b8e873 b8e607
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e607
          have b8e4373 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
          clear b8e4372
          have b8e4552 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e256 (σ x) (σ y)
               have i₂ := b8e4373
               grind)
            | exact superpose b8e4373 b8e256
            | exact resolve b8e256 b8e4373
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4373
          have b8e5174 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e3225 x
               have i₂ := b8e4552
               grind)
            | exact superpose b8e4552 b8e3225
            | exact resolve b8e3225 b8e4552
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3225 b8e4552
          have b8e5249 : x = (k x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e5174
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e5174
            | exact resolve b8e5174 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5174
          have b8e5410 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e1790 x x
               have i₂ := b8e5249
               grind)
            | exact superpose b8e5249 b8e1790
            | (have j0 := b8e1790 x x
               grind)
            | (have r₁ := b8e1790 x x
               have r₂ := b8e5249
               grind)
            | exact resolve b8e1790 b8e5249
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1790 b8e5249
          have b8e5414 : x = (M.op x x) ∨ x = (M.op x y) := by grind
          clear b8e5410
          have b8e5781 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e13 X0 x x
               have i₂ := b8e5414
               grind)
            | exact superpose b8e5414 b8e13
            | exact resolve b8e13 b8e5414
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e5819 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e302 x x x
               have i₂ := b8e5414
               grind)
            | exact superpose b8e5414 b8e302
            | exact resolve b8e302 b8e5414
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5414
          have b8e5822 : ∀ X0 : G, x = (M.op (M.op x X0) x) ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e5819 X0
               have i₂ := b8e256 x X0
               grind)
            | exact superpose b8e256 b8e5819
            | exact resolve b8e5819 b8e256
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5819
          have b8e7489 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e5781 X0
               have i₂ := b8e5822 X0
               grind)
            | exact superpose b8e5822 b8e5781
            | exact resolve b8e5781 b8e5822
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5781 b8e5822
          have b8e7565 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (M.op x y) := by
            intro X0
            first
            | (have j0 := b8e7489 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7489
          have b8e7879 : ∀ X0 : G, x = (M.op x x) ∨ (M.op x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e256 x y
               have i₂ := b8e7565 X0
               grind)
            | exact superpose b8e7565 b8e256
            | (have j1 := b8e7565 x
               grind)
            | exact resolve b8e256 b8e7565
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7565
          have b8e8338 : x ≠ x ∨ x = (M.op x x) := by
            first
            | (have j0 := b8e7879 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7879
          have b8e8339 : x = (M.op x x) := by grind
          clear b8e8338
          have b8e8518 : x = (k x x) := by
            first
            | (have i₁ := b8e3031 x
               have i₂ := b8e8339
               grind)
            | exact superpose b8e8339 b8e3031
            | exact resolve b8e3031 b8e8339
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3031
          have b8e8520 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e13 X0 x x
               have i₂ := b8e8339
               grind)
            | exact superpose b8e8339 b8e13
            | exact resolve b8e13 b8e8339
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e8570 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
            intro X0
            first
            | (have i₁ := b8e302 x x x
               have i₂ := b8e8339
               grind)
            | exact superpose b8e8339 b8e302
            | exact resolve b8e302 b8e8339
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e302 b8e8339
          have b8e8573 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
            intro X0
            first
            | (have i₁ := b8e8570 X0
               have i₂ := b8e256 x X0
               grind)
            | exact superpose b8e256 b8e8570
            | exact resolve b8e8570 b8e256
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e256 b8e8570
          have b8e8894 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e895 x x
               have i₂ := b8e8518
               grind)
            | exact superpose b8e8518 b8e895
            | (have j0 := b8e895 x x
               grind)
            | exact resolve b8e895 b8e8518
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e895 b8e8518
          have b8e8900 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b8e8894
          have b8e10607 : ∀ X0 : G, (M.op x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e8520 X0
               have i₂ := b8e8573 X0
               grind)
            | exact superpose b8e8573 b8e8520
            | exact resolve b8e8520 b8e8573
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e10685 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op x (τ X0)) x))) ∨ (τ X0) = (M.op (M.op x (τ X0)) x) := by
            intro X0
            first
            | (have i₁ := b8e97 (M.op (M.op x (τ x)) x) x
               have i₂ := b8e8520 (τ x)
               grind)
            | exact superpose b8e8520 b8e97
            | exact resolve b8e97 b8e8520
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e97 b8e8520
          have b8e10686 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) ∨ (τ X0) = (M.op (M.op x (τ X0)) x) := by
            intro X0
            first
            | (have i₁ := b8e10685 X0
               have i₂ := b8e8573 (τ X0)
               grind)
            | exact superpose b8e8573 b8e10685
            | (have j0 := b8e10685 X0
               grind)
            | exact resolve b8e10685 b8e8573
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10685
          have b8e10719 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (τ X0) = (M.op (M.op x (τ X0)) x) := by
            intro X0
            first
            | (have i₁ := b8e10686 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e10686
            | (have j0 := b8e10686 X0
               grind)
            | exact resolve b8e10686 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10686
          have b8e10746 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (τ X0) = x := by
            intro X0
            first
            | (have i₁ := b8e10719 X0
               have i₂ := b8e8573 (τ X0)
               grind)
            | exact superpose b8e8573 b8e10719
            | (have j0 := b8e10719 X0
               grind)
            | exact resolve b8e10719 b8e8573
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10719
          have b8e11068 : ∀ X0 : G, x = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b8e8573 X0
               have i₂ := b8e10607 X0
               grind)
            | exact superpose b8e10607 b8e8573
            | exact resolve b8e8573 b8e10607
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8573
          have b8e11703 : x ≠ y := by
            first
            | (have i₁ := b8e22
               have i₂ := b8e11068 y
               grind)
            | exact superpose b8e11068 b8e22
            | exact resolve b8e22 b8e11068
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11068
          have b8e15205 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ x))) ∨ (τ (σ X0)) = x := by
            intro X0
            first
            | (have i₁ := b8e39 X0 (σ x)
               have i₂ := b8e10746 (σ X0)
               grind)
            | exact superpose b8e10746 b8e39
            | (have j1 := b8e10746 (σ X0)
               grind)
            | exact resolve b8e39 b8e10746
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e39 b8e10746
          have b8e15268 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) ∨ (τ (σ X0)) = x := by
            intro X0
            first
            | (have i₁ := b8e15205 X0
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e15205
            | (have j0 := b8e15205 X0
               grind)
            | exact resolve b8e15205 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15205
          have b8e15300 : ∀ X0 : G, (k X0 x) = X0 ∨ (τ (σ X0)) = x := by
            intro X0
            first
            | (have i₁ := b8e15268 X0
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e15268
            | (have j0 := b8e15268 X0
               grind)
            | exact resolve b8e15268 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15268
          have b8e15311 : ∀ X0 : G, (k X0 x) = X0 ∨ x = X0 := by
            intro X0
            first
            | (have i₁ := b8e15300 X0
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e15300
            | (have j0 := b8e15300 X0
               grind)
            | exact resolve b8e15300 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15300
          have b8e15402 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
            first
            | (have i₁ := b8e873
               have i₂ := b8e15311 y
               grind)
            | exact superpose b8e15311 b8e873
            | (have j1 := b8e15311 y
               grind)
            | exact resolve b8e873 b8e15311
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e873
          have b8e15403 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e15402
               have r₂ := b8e11703
               grind)
            | exact resolve b8e15402 b8e11703
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15402
          have b8e15432 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e15403
               have i₂ := b8e10607 y
               grind)
            | exact superpose b8e10607 b8e15403
            | exact resolve b8e15403 b8e10607
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15403
          have b8e15433 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b8e15432
          have b8e15455 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e15433
               grind)
            | exact superpose b8e15433 b8e20
            | exact resolve b8e20 b8e15433
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e15466 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e15433
               grind)
            | exact superpose b8e15433 b8e17
            | (have j0 := b8e17 (σ y) (σ x)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e15433
               grind)
            | exact resolve b8e17 b8e15433
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15433
          have b8e15520 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
          clear b8e15466
          have b8e15528 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b8e15520
               have i₂ := b8e8900
               grind)
            | exact superpose b8e8900 b8e15520
            | exact resolve b8e15520 b8e8900
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8900 b8e15520
          have b8e15536 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b8e15455
               have i₂ := b8e10607 y
               grind)
            | exact superpose b8e10607 b8e15455
            | exact resolve b8e15455 b8e10607
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10607 b8e15455
          have b8e15541 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e15528
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e15528
            | exact resolve b8e15528 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15528
          have b8e15545 : (σ x) = (σ (k y x)) := by
            first
            | (have r₁ := b8e15541
               have r₂ := b8e15536
               grind)
            | exact resolve b8e15541 b8e15536
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15541
          have b8e16055 : (σ x) = (σ y) ∨ x = y := by
            first
            | (have i₁ := b8e15545
               have i₂ := b8e15311 y
               grind)
            | exact superpose b8e15311 b8e15545
            | (have j1 := b8e15311 y
               grind)
            | exact resolve b8e15545 b8e15311
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15311 b8e15545
          have b8e16155 : x = y := by
            first
            | (have r₁ := b8e16055
               have r₂ := b8e15536
               grind)
            | exact resolve b8e16055 b8e15536
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15536 b8e16055
          have b8e16164 : False := by grind
          exact b8e16164

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(Y,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_y_pyy_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op y y) := by grind
      have b0e20 : (σ x) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
           have i₂ := b0e11 X0 X1 X2
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e151 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e33 X0 x x X0
           have i₂ := b0e11 X0 x x
           grind)
        | exact superpose b0e11 b0e33
        | exact resolve b0e33 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e157 : (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e151 (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e151
        | exact resolve b0e151 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e158 : y = (M.op x y) := by
        first
        | (have i₁ := b0e151 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e151
        | exact resolve b0e151 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e151
      have b0e218 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e157
           grind)
        | exact superpose b0e157 b0e18
        | exact resolve b0e18 b0e157
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e157
      have b0e227 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e218
           have i₂ := b0e158
           grind)
        | exact superpose b0e158 b0e218
        | exact resolve b0e218 b0e158
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e158 b0e218
      have b0e228 : False := by grind
      exact b0e228
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op y y) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : y = (k x y) := by grind
        have b1e31 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e12 X0 (σ y) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e37 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e16 (σ x) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e16
          | (have j0 := b1e16 (σ x) (σ y)
             grind)
          | (have r₁ := b1e16 (σ x) (σ y)
             have r₂ := b1e22
             grind)
          | exact resolve b1e16 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e40 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b1e37
        have b1e41 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e40
             have r₂ := b1e21
             grind)
          | exact resolve b1e40 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40
        have b1e42 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e41
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e41
          | exact resolve b1e41 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41
        have b1e43 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e42
             have i₂ := b1e24
             grind)
          | exact superpose b1e24 b1e42
          | exact resolve b1e42 b1e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e42
        have b1e59 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e43
             grind)
          | exact superpose b1e43 b1e21
          | exact resolve b1e21 b1e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e99 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) := by
          first
          | (have i₁ := b1e31 (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e31
          | exact resolve b1e31 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31
        have b1e106 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b1e99
             have i₂ := b1e43
             grind)
          | exact superpose b1e43 b1e99
          | exact resolve b1e99 b1e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43 b1e99
        have b1e107 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e106
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e106
          | exact resolve b1e106 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e106
        have b1e108 : False := by grind
        exact b1e108
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : x = (M.op y y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : y = (k x y) := by grind
        have b2e28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e50 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e17 X0 (σ y)
             grind)
          | (have i₁ := b2e21
             have i₂ := b2e17 (M.op (σ y) (σ y)) x
             grind)
          | exact superpose b2e17 b2e21
          | (have j1 := b2e17 X0 (σ y)
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | exact resolve b2e21 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e86 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e28 X0 x x X0
             have i₂ := b2e12 X0 x x
             grind)
          | exact superpose b2e12 b2e28
          | exact resolve b2e28 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28
        have b2e91 : y = (M.op x y) := by
          first
          | (have i₁ := b2e86 y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e86
          | exact resolve b2e86 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e86
        have b2e162 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e50 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50
        have b2e163 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e162
             have r₂ := b2e22
             grind)
          | exact resolve b2e162 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e162
        have b2e164 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e163
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e163
          | exact resolve b2e163 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e163
        have b2e165 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e164
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e164
          | exact resolve b2e164 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e164
        have b2e213 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e165
             grind)
          | exact superpose b2e165 b2e19
          | exact resolve b2e19 b2e165
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e165
        have b2e224 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e213
             have i₂ := b2e91
             grind)
          | exact superpose b2e91 b2e213
          | exact resolve b2e213 b2e91
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e91 b2e213
        have b2e225 : False := by grind
        exact b2e225
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : x ≠ (M.op y y) := by grind
        have b3e21 : y = (M.op y x) := by grind
        have b3e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e24 : (σ y) = (k (σ x) (σ y)) := by grind
        have b3e25 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b3e24
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e24
          | exact resolve b3e24 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e26 : (k x y) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (k x y)
             have i₂ := b3e25
             grind)
          | exact superpose b3e25 b3e13
          | exact resolve b3e13 b3e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25
        have b3e27 : y = (k x y) := by
          first
          | (have i₁ := b3e26
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e26
          | exact resolve b3e26 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26
        have b3e38 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) := by
          intro X0
          first
          | (have i₁ := b3e12 x y X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e44 : x = (M.op (M.op y y) x) := by
          first
          | (have i₁ := b3e38 x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e38
          | exact resolve b3e38 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38
        have b3e47 : y ≠ y ∨ x = (M.op y y) ∨ (M.op y y) = (k x y) := by
          first
          | (have i₁ := b3e16 x y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e16
          | (have j0 := b3e16 x y
             grind)
          | (have r₁ := b3e16 x y
             have r₂ := b3e21
             grind)
          | exact resolve b3e16 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e51 : x = (M.op y y) ∨ (M.op y y) = (k x y) := by grind
        clear b3e47
        have b3e52 : (M.op y y) = (k x y) := by
          first
          | (have r₁ := b3e51
             have r₂ := b3e20
             grind)
          | exact resolve b3e51 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e51
        have b3e53 : y = (M.op y y) := by
          first
          | (have i₁ := b3e52
             have i₂ := b3e27
             grind)
          | exact superpose b3e27 b3e52
          | exact resolve b3e52 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27 b3e52
        have b3e54 : x ≠ y := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e53
             grind)
          | exact superpose b3e53 b3e20
          | exact resolve b3e20 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e94 : x = (M.op y x) := by
          first
          | (have i₁ := b3e44
             have i₂ := b3e53
             grind)
          | exact superpose b3e53 b3e44
          | exact resolve b3e44 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44 b3e53
        have b3e100 : x = y := by
          first
          | (have i₁ := b3e94
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e94
          | exact resolve b3e94 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e94
        have b3e101 : False := by grind
        exact b3e101
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
            intro X0 X1 X2
            grind
          have b4e21 : x ≠ (M.op y y) := by grind
          have b4e22 : y = (M.op y x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e28 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) := by
            intro X0
            first
            | (have i₁ := b4e13 x y X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e31 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
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
          have b4e34 : x = (M.op (M.op y y) x) := by
            first
            | (have i₁ := b4e28 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e28
            | exact resolve b4e28 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28
          have b4e137 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e30 X0 x x X0
               have i₂ := b4e13 X0 x x
               grind)
            | exact superpose b4e13 b4e30
            | exact resolve b4e30 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30
          have b4e148 : y = (M.op y y) := by
            first
            | (have i₁ := b4e31 y
               have i₂ := b4e137 y
               grind)
            | exact superpose b4e137 b4e31
            | exact resolve b4e31 b4e137
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31 b4e137
          have b4e196 : x = (M.op y x) := by
            first
            | (have i₁ := b4e34
               have i₂ := b4e148
               grind)
            | exact superpose b4e148 b4e34
            | exact resolve b4e34 b4e148
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e197 : x ≠ y := by
            first
            | (have i₁ := b4e21
               have i₂ := b4e148
               grind)
            | exact superpose b4e148 b4e21
            | exact resolve b4e21 b4e148
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e148
          have b4e208 : x = y := by
            first
            | (have i₁ := b4e196
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e196
            | exact resolve b4e196 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e196
          have b4e209 : False := by grind
          exact b4e209
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
            intro X0 X1 X2
            grind
          have b5e21 : x ≠ (M.op y y) := by grind
          have b5e22 : y = (M.op y x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e28 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) := by
            intro X0
            first
            | (have i₁ := b5e13 x y X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e30 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
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
          have b5e32 : x = (M.op (M.op y y) x) := by
            first
            | (have i₁ := b5e28 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e28
            | exact resolve b5e28 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28
          have b5e100 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e29 X0 x x X0
               have i₂ := b5e13 X0 x x
               grind)
            | exact superpose b5e13 b5e29
            | exact resolve b5e29 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29
          have b5e108 : y = (M.op y y) := by
            first
            | (have i₁ := b5e30 y
               have i₂ := b5e100 y
               grind)
            | exact superpose b5e100 b5e30
            | exact resolve b5e30 b5e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e100
          have b5e144 : x = (M.op y x) := by
            first
            | (have i₁ := b5e32
               have i₂ := b5e108
               grind)
            | exact superpose b5e108 b5e32
            | exact resolve b5e32 b5e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e145 : x ≠ y := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e108
               grind)
            | exact superpose b5e108 b5e21
            | exact resolve b5e21 b5e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e108
          have b5e156 : x = y := by
            first
            | (have i₁ := b5e144
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e144
            | exact resolve b5e144 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e144
          have b5e157 : False := by grind
          exact b5e157
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
          intro X0 X1 X2
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : x ≠ (M.op y y) := by grind
        have b6e21 : y ≠ (M.op y x) := by grind
        have b6e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e24 : (σ y) = (k (σ x) (σ y)) := by grind
        have b6e25 : (σ y) = (σ (k x y)) := by
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
        have b6e39 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
             have i₂ := b6e12 X0 X1 X2
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e75 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
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
        have b6e82 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e75
             have r₂ := b6e20
             grind)
          | exact resolve b6e75 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e75
        have b6e85 : (σ (M.op x y)) = (σ y) := by
          first
          | (have r₁ := b6e82
             have r₂ := b6e21
             grind)
          | exact resolve b6e82 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e82
        have b6e130 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b6e39 X0 x x X0
             have i₂ := b6e12 X0 x x
             grind)
          | exact superpose b6e12 b6e39
          | exact resolve b6e39 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39
        have b6e136 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e130 (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e130
          | exact resolve b6e130 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e130
        have b6e190 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e136
             grind)
          | exact superpose b6e136 b6e19
          | exact resolve b6e19 b6e136
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e136
        have b6e199 : False := by grind
        exact b6e199
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
            intro X0 X1 X2
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e30 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 := by
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
          have b7e36 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
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
          have b7e38 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b7e36
          have b7e39 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e38
               have r₂ := b7e23
               grind)
            | exact resolve b7e38 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e38
          have b7e40 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e39
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e39
            | exact resolve b7e39 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39
          have b7e70 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) := by
            first
            | (have i₁ := b7e30 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e30
            | exact resolve b7e30 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e76 : (σ x) = (M.op (σ (k x y)) (σ x)) := by
            first
            | (have i₁ := b7e70
               have i₂ := b7e40
               grind)
            | exact superpose b7e40 b7e70
            | exact resolve b7e70 b7e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e102 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e29 X0 x x X0
               have i₂ := b7e13 X0 x x
               grind)
            | exact superpose b7e13 b7e29
            | exact resolve b7e29 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29
          have b7e111 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e30 (σ y)
               have i₂ := b7e102 (σ y)
               grind)
            | exact superpose b7e102 b7e30
            | exact resolve b7e30 b7e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e102
          have b7e147 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e40
               have i₂ := b7e111
               grind)
            | exact superpose b7e111 b7e40
            | exact resolve b7e40 b7e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40
          have b7e148 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e111
               grind)
            | exact superpose b7e111 b7e23
            | exact resolve b7e23 b7e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e111
          have b7e779 : (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b7e76
               have i₂ := b7e147
               grind)
            | exact superpose b7e147 b7e76
            | exact resolve b7e76 b7e147
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e76 b7e147
          have b7e807 : (σ x) = (σ y) := by
            first
            | (have i₁ := b7e779
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e779
            | exact resolve b7e779 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e779
          have b7e818 : False := by grind
          exact b7e818
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op y y) := by grind
          have b8e22 : y ≠ (M.op y x) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e55 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 X0 (σ y)
               grind)
            | (have i₁ := b8e23
               have i₂ := b8e18 (M.op (σ y) (σ y)) x
               grind)
            | exact superpose b8e18 b8e23
            | (have j1 := b8e18 X0 (σ y)
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e143 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b8e55 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55
          have b8e144 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e143
               have r₂ := b8e24
               grind)
            | exact resolve b8e143 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e143
          have b8e145 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e144
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e144
            | exact resolve b8e144 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e144
          have b8e195 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e145
               grind)
            | exact superpose b8e145 b8e20
            | exact resolve b8e20 b8e145
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e145
          have b8e241 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e195
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e195
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e195 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e195
          have b8e242 : x = (M.op y y) ∨ y = (M.op y x) := by grind
          clear b8e241
          have b8e244 : y = (M.op y x) := by
            first
            | (have r₁ := b8e242
               have r₂ := b8e21
               grind)
            | exact resolve b8e242 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e242
          have b8e246 : False := by grind
          exact b8e246
