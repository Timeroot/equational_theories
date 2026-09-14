import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(X,X),X) = m(Y,X) then m(Y,X) else if m(X,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppxxx_pyx_pxx_y_pyx_pxx_pyx_Equation1 :
    AutBox.GuardAut2 (((Lf 0) ⋆ (Lf 0)) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 0) ⋆ (Lf 0)) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op a a) a ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op a a) a = M.op b a ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op a a) a = M.op b a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op x x) x) (M.op y x) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e32 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
        intro X0
        first
        | (have j0 := b0e14 X0 (M.op X0 X0)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e47 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X2 X1) = (k X1 X2) ∨ (M.op X1 X1) = X2 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e16 X1 X2
           have i₂ := b0e16 X1 X0
           grind)
        | (have i₁ := b0e16 X0 X1
           have i₂ := b0e16 X0 (M.op X0 X0)
           grind)
        | exact superpose b0e16 b0e16
        | (have j0 := b0e16 X1 X2
           have j1 := b0e16 X1 X2
           grind)
        | exact resolve b0e16 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e49 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X2 X1) = (k X1 X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e14 X1 X2
           have i₂ := b0e16 X1 X0
           grind)
        | (have i₁ := b0e14 X0 X1
           have i₂ := b0e16 X0 (M.op X0 X0)
           grind)
        | exact superpose b0e16 b0e14
        | (have j0 := b0e14 X1 X2
           have j1 := b0e16 X1 X0
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | (have r₁ := b0e14 X0 (M.op X0 X0)
           have r₂ := b0e16 X0 (M.op X0 X0)
           grind)
        | (have r₁ := b0e14 X0 X0
           have r₂ := b0e16 X0 (M.op (M.op X0 X0) X0)
           grind)
        | exact resolve b0e14 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e62 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k X1 X2) ∨ (M.op X1 X1) = X2 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
        intro X0 X1 X2
        first
        | (have j0 := b0e47 X2 X1 X2
           have j1 := b0e49 X2 X1 X2
           grind)
        | (have r₁ := b0e47 X0 X1 X2
           have r₂ := b0e49 X0 X1 X2
           grind)
        | (have r₁ := b0e47 X2 X1 X0
           have r₂ := b0e49 X0 X1 X2
           grind)
        | (have r₁ := b0e47 X0 X1 (M.op X2 X1)
           have r₂ := b0e49 X1 X1 X2
           grind)
        | exact resolve b0e47 b0e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47 b0e49
      have b0e272 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e62 X0 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e62
      have b0e273 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e272 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e272
      have b0e274 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e273 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e273
      have b0e433 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e32 X1
           have i₂ := b0e274 X0 X1
           grind)
        | (have i₁ := b0e32 X0
           have i₂ := b0e274 (M.op X0 X0) X1
           grind)
        | exact superpose b0e274 b0e32
        | (have j1 := b0e274 X0 X1
           grind)
        | exact resolve b0e32 b0e274
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32 b0e274
      have b0e448 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e433 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e433
      have b0e606 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X1 X0
           have i₂ := b0e448 (σ X0) (σ X1)
           grind)
        | exact superpose b0e448 b0e17
        | exact resolve b0e17 b0e448
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e623 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e606 X0 X1
           have i₂ := b0e448 X0 X1
           grind)
        | exact superpose b0e448 b0e606
        | exact resolve b0e606 b0e448
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e448 b0e606
      have b0e1494 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e623 x y
           grind)
        | exact superpose b0e623 b0e18
        | (have r₁ := b0e18
           have r₂ := b0e623 x y
           grind)
        | exact resolve b0e18 b0e623
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e623
      have b0e1516 : False := by grind
      exact b0e1516
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e21 : (M.op (M.op (σ x) (σ x)) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e25 : False := by grind
        exact b1e25
      · have b2e15 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e40 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
          intro X0
          first
          | (have j0 := b2e15 X0 (M.op X0 X0)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e52 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X2 X1) = (k X1 X2) ∨ (M.op X1 X1) = X2 ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e17 X1 X2
             have i₂ := b2e17 X1 X0
             grind)
          | (have i₁ := b2e17 X0 X1
             have i₂ := b2e17 X0 (M.op X0 X0)
             grind)
          | exact superpose b2e17 b2e17
          | (have j0 := b2e17 X1 X2
             have j1 := b2e17 X1 X2
             grind)
          | exact resolve b2e17 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e56 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X2 X1) = (k X1 X2) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 X1 X2
             have i₂ := b2e17 X1 X0
             grind)
          | (have i₁ := b2e15 X0 X1
             have i₂ := b2e17 X0 (M.op X0 X0)
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X1 X2
             have j1 := b2e17 X1 X0
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X0 (M.op X0 X0)
             have r₂ := b2e17 X0 (M.op X0 X0)
             grind)
          | (have r₁ := b2e15 X0 X0
             have r₂ := b2e17 X0 (M.op (M.op X0 X0) X0)
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e67 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k X1 X2) ∨ (M.op X1 X1) = X2 ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have j0 := b2e52 X2 X1 X2
             have j1 := b2e56 X2 X1 X2
             grind)
          | (have r₁ := b2e52 X0 X1 X2
             have r₂ := b2e56 X0 X1 X2
             grind)
          | (have r₁ := b2e52 X2 X1 X0
             have r₂ := b2e56 X0 X1 X2
             grind)
          | (have r₁ := b2e52 X0 X1 (M.op X2 X1)
             have r₂ := b2e56 X1 X1 X2
             grind)
          | exact resolve b2e52 b2e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52 b2e56
        have b2e186 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b2e67 X0 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e67
        have b2e187 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e186 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e186
        have b2e188 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e187 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e187
        have b2e213 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e40 X1
             have i₂ := b2e188 X0 X1
             grind)
          | (have i₁ := b2e40 X0
             have i₂ := b2e188 (M.op X0 X0) X1
             grind)
          | exact superpose b2e188 b2e40
          | (have j1 := b2e188 X0 X1
             grind)
          | exact resolve b2e40 b2e188
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40 b2e188
        have b2e221 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b2e213 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e213
        have b2e240 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e221 (σ X0) (σ X1)
             grind)
          | exact superpose b2e221 b2e18
          | exact resolve b2e18 b2e221
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e247 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e240 X0 X1
             have i₂ := b2e221 X0 X1
             grind)
          | exact superpose b2e221 b2e240
          | exact resolve b2e240 b2e221
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e221 b2e240
        have b2e818 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e247 x y
             grind)
          | exact superpose b2e247 b2e19
          | (have r₁ := b2e19
             have r₂ := b2e247 x y
             grind)
          | exact resolve b2e19 b2e247
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e247
        have b2e836 : False := by grind
        exact b2e836
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
      · have b3e20 : (M.op (M.op x x) x) ≠ (M.op y x) := by grind
        have b3e21 : y = (M.op x x) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e24 : (M.op y x) ≠ (M.op y x) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e20
          | exact resolve b3e20 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e25 : False := by grind
        exact b3e25
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e23 : (M.op (M.op (σ x) (σ x)) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e26 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e23
            | exact resolve b4e23 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e27 : False := by grind
          exact b4e27
        · have b5e21 : (M.op (M.op x x) x) ≠ (M.op y x) := by grind
          have b5e22 : y = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e26 : (M.op y x) ≠ (M.op y x) := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e21
            | exact resolve b5e21 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e27 : False := by grind
          exact b5e27
    · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op (M.op x x) x) ≠ (M.op y x) := by grind
        have b6e21 : y ≠ (M.op x x) := by grind
        have b6e22 : (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e25 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X1 (τ X0)
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e18
          | exact resolve b6e18 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e35 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e13 (k X0 (τ X1))
             have i₂ := b6e25 X1 X0
             grind)
          | exact superpose b6e25 b6e13
          | exact resolve b6e13 b6e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e38 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b6e15 (σ x) X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e15
          | (have j0 := b6e15 (σ x) X0
             grind)
          | (have r₁ := b6e15 (σ x) (σ y)
             have r₂ := b6e22
             grind)
          | exact resolve b6e15 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e40 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
          intro X0
          first
          | (have j0 := b6e15 X0 (M.op X0 X0)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e52 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X2 X1) = (k X1 X2) ∨ (M.op X1 X1) = X2 ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e17 X1 X2
             have i₂ := b6e17 X1 X0
             grind)
          | (have i₁ := b6e17 X0 X1
             have i₂ := b6e17 X0 (M.op X0 X0)
             grind)
          | exact superpose b6e17 b6e17
          | (have j0 := b6e17 X1 X2
             have j1 := b6e17 X1 X2
             grind)
          | exact resolve b6e17 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e54 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X2 X1) = (k X1 X2) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e15 X1 X2
             have i₂ := b6e17 X1 X0
             grind)
          | (have i₁ := b6e15 X0 X1
             have i₂ := b6e17 X0 (M.op X0 X0)
             grind)
          | exact superpose b6e17 b6e15
          | (have j0 := b6e15 X1 X2
             have j1 := b6e17 X1 X0
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X0 (M.op X0 X0)
             have r₂ := b6e17 X0 (M.op X0 X0)
             grind)
          | (have r₁ := b6e15 X0 X0
             have r₂ := b6e17 X0 (M.op (M.op X0 X0) X0)
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e56 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ (M.op (σ x) (σ x)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e22
             have i₂ := b6e17 (σ x) X0
             grind)
          | (have i₁ := b6e22
             have i₂ := b6e17 (σ x) (M.op (σ x) (σ x))
             grind)
          | exact superpose b6e17 b6e22
          | (have j1 := b6e17 (σ x) X0
             grind)
          | exact resolve b6e22 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e57 : ∀ X0 : G, (M.op y x) ≠ (M.op X0 x) ∨ (M.op X0 x) = (k x X0) ∨ (M.op x x) = X0 := by
          intro X0
          first
          | (have i₁ := b6e20
             have i₂ := b6e17 x X0
             grind)
          | (have i₁ := b6e20
             have i₂ := b6e17 x (M.op x x)
             grind)
          | exact superpose b6e17 b6e20
          | (have j1 := b6e17 x X0
             grind)
          | (have r₁ := b6e20
             have r₂ := b6e17 x y
             grind)
          | exact resolve b6e20 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e65 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ x) X0) ∨ (M.op (σ x) (σ x)) = X0 := by
          intro X0
          first
          | (have j0 := b6e56 X0
             have j1 := b6e38 X0
             grind)
          | (have r₁ := b6e56 X0
             have r₂ := b6e38 X0
             grind)
          | (have r₁ := b6e56 (σ y)
             have r₂ := b6e38 (σ y)
             grind)
          | (have r₁ := b6e56 (M.op (σ y) (σ x))
             have r₂ := b6e38 (σ x)
             grind)
          | exact resolve b6e56 b6e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38 b6e56
        have b6e67 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k X1 X2) ∨ (M.op X1 X1) = X2 ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
          intro X0 X1 X2
          first
          | (have j0 := b6e52 X2 X1 X2
             have j1 := b6e54 X2 X1 X2
             grind)
          | (have r₁ := b6e52 X0 X1 X2
             have r₂ := b6e54 X0 X1 X2
             grind)
          | (have r₁ := b6e52 X2 X1 X0
             have r₂ := b6e54 X0 X1 X2
             grind)
          | (have r₁ := b6e52 X0 X1 (M.op X2 X1)
             have r₂ := b6e54 X1 X1 X2
             grind)
          | exact resolve b6e52 b6e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e52 b6e54
        have b6e103 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ x) X0) ∨ (M.op X0 (σ x)) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b6e40 (σ x)
             have i₂ := b6e65 X0
             grind)
          | (have i₁ := b6e40 X0
             have i₂ := b6e65 (M.op X0 X0)
             grind)
          | exact superpose b6e65 b6e40
          | (have j1 := b6e65 X0
             grind)
          | exact resolve b6e40 b6e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e65
        have b6e108 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ x) X0) := by
          intro X0
          first
          | (have j0 := b6e103 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e103
        have b6e115 : ∀ X0 : G, (k x (τ X0)) = (τ (M.op X0 (σ x))) := by
          intro X0
          first
          | (have i₁ := b6e35 x X0
             have i₂ := b6e108 X0
             grind)
          | exact superpose b6e108 b6e35
          | exact resolve b6e35 b6e108
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35 b6e108
        have b6e144 : (M.op y x) = (k x y) ∨ y = (M.op x x) := by
          first
          | (have j0 := b6e57 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e57
        have b6e146 : (M.op y x) = (k x y) := by
          first
          | (have r₁ := b6e144
             have r₂ := b6e21
             grind)
          | exact resolve b6e144 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e144
        have b6e189 : (k x (τ (M.op (σ x) (σ x)))) = (τ (M.op (σ y) (σ x))) := by
          first
          | (have i₁ := b6e115 (M.op (σ x) (σ x))
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e115
          | exact resolve b6e115 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e202 : (k x (τ (M.op (σ x) (σ x)))) = (k x (τ (σ y))) := by
          first
          | (have i₁ := b6e189
             have i₂ := b6e115 (σ y)
             grind)
          | exact superpose b6e115 b6e189
          | exact resolve b6e189 b6e115
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e189
        have b6e203 : (k x y) = (k x (τ (M.op (σ x) (σ x)))) := by
          first
          | (have i₁ := b6e202
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e202
          | exact resolve b6e202 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e202
        have b6e204 : (k x y) = (k x (k x (τ (σ x)))) := by
          first
          | (have i₁ := b6e203
             have i₂ := b6e115 (σ x)
             grind)
          | exact superpose b6e115 b6e203
          | exact resolve b6e203 b6e115
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e115 b6e203
        have b6e205 : (k x y) = (k x (k x x)) := by
          first
          | (have i₁ := b6e204
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e204
          | exact resolve b6e204 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e204
        have b6e206 : (M.op y x) = (k x (k x x)) := by
          first
          | (have i₁ := b6e205
             have i₂ := b6e146
             grind)
          | exact superpose b6e146 b6e205
          | exact resolve b6e205 b6e146
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e146 b6e205
        have b6e258 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b6e67 X0 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e67
        have b6e259 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e258 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e258
        have b6e260 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e259 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e259
        have b6e433 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e40 X1
             have i₂ := b6e260 X0 X1
             grind)
          | (have i₁ := b6e40 X0
             have i₂ := b6e260 (M.op X0 X0) X1
             grind)
          | exact superpose b6e260 b6e40
          | (have j1 := b6e260 X0 X1
             grind)
          | exact resolve b6e40 b6e260
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40 b6e260
        have b6e448 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b6e433 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e433
        have b6e1132 : (M.op y x) = (M.op (k x x) x) := by
          first
          | (have i₁ := b6e206
             have i₂ := b6e448 (k x x) x
             grind)
          | exact superpose b6e448 b6e206
          | exact resolve b6e206 b6e448
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e206
        have b6e1133 : (M.op (M.op x x) x) = (M.op y x) := by
          first
          | (have i₁ := b6e1132
             have i₂ := b6e448 x x
             grind)
          | exact superpose b6e448 b6e1132
          | exact resolve b6e1132 b6e448
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e448 b6e1132
        have b6e1158 : False := by grind
        exact b6e1158
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e23 : (M.op (M.op (σ x) (σ x)) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e27 : False := by grind
          exact b7e27
        · have b8e16 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e32 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
            intro X0
            first
            | (have j0 := b8e16 X0 (M.op X0 X0)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e41 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X2 X1) = (k X1 X2) ∨ (M.op X1 X1) = X2 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e18 X1 X2
               have i₂ := b8e18 X1 X0
               grind)
            | (have i₁ := b8e18 X0 X1
               have i₂ := b8e18 X0 (M.op X0 X0)
               grind)
            | exact superpose b8e18 b8e18
            | (have j0 := b8e18 X1 X2
               have j1 := b8e18 X1 X2
               grind)
            | exact resolve b8e18 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e45 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X2 X1) = (k X1 X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e16 X1 X2
               have i₂ := b8e18 X1 X0
               grind)
            | (have i₁ := b8e16 X0 X1
               have i₂ := b8e18 X0 (M.op X0 X0)
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X1 X2
               have j1 := b8e18 X1 X0
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 (M.op X0 X0)
               have r₂ := b8e18 X0 (M.op X0 X0)
               grind)
            | (have r₁ := b8e16 X0 X0
               have r₂ := b8e18 X0 (M.op (M.op X0 X0) X0)
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e54 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k X1 X2) ∨ (M.op X1 X1) = X2 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have j0 := b8e41 X2 X1 X2
               have j1 := b8e45 X2 X1 X2
               grind)
            | (have r₁ := b8e41 X0 X1 X2
               have r₂ := b8e45 X0 X1 X2
               grind)
            | (have r₁ := b8e41 X2 X1 X0
               have r₂ := b8e45 X0 X1 X2
               grind)
            | (have r₁ := b8e41 X0 X1 (M.op X2 X1)
               have r₂ := b8e45 X1 X1 X2
               grind)
            | exact resolve b8e41 b8e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e41 b8e45
          have b8e173 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e54 X0 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e54
          have b8e174 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e173 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e173
          have b8e175 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e174 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e174
          have b8e200 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e32 X1
               have i₂ := b8e175 X0 X1
               grind)
            | (have i₁ := b8e32 X0
               have i₂ := b8e175 (M.op X0 X0) X1
               grind)
            | exact superpose b8e175 b8e32
            | (have j1 := b8e175 X0 X1
               grind)
            | exact resolve b8e32 b8e175
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32 b8e175
          have b8e208 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e200 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e200
          have b8e227 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e208 (σ X0) (σ X1)
               grind)
            | exact superpose b8e208 b8e19
            | exact resolve b8e19 b8e208
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e234 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e227 X0 X1
               have i₂ := b8e208 X0 X1
               grind)
            | exact superpose b8e208 b8e227
            | exact resolve b8e227 b8e208
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e208 b8e227
          have b8e796 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e234 x y
               grind)
            | exact superpose b8e234 b8e20
            | (have r₁ := b8e20
               have r₂ := b8e234 x y
               grind)
            | exact resolve b8e20 b8e234
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e234
          have b8e814 : False := by grind
          exact b8e814

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(X,X),X) = m(Y,Y) then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppxxx_pyy_x_y_pxy_pxx_pxy_Equation1 :
    AutBox.GuardAut2 (((Lf 0) ⋆ (Lf 0)) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 0) ⋆ (Lf 0)) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op a a) a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op a a) a = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op a a) a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op x x) x) (M.op y y) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op (M.op x x) x) = (M.op y y) := by grind
      have b0e20 : (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e28 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op y y) ∨ (k x X0) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b0e14 x X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 x X0
           grind)
        | (have r₁ := b0e14 x y
           have r₂ := b0e19
           grind)
        | exact resolve b0e14 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e29 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ y) (σ y)) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e14 (σ x) X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have j0 := b0e14 (σ x) X0
           grind)
        | (have r₁ := b0e14 (σ x) (σ y)
           have r₂ := b0e20
           grind)
        | exact resolve b0e14 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e114 : (M.op x y) = (k x y) := by
        first
        | (have j0 := b0e28 y
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28
      have b0e156 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have j0 := b0e29 (σ y)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29
      have b0e157 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e156
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e156
        | exact resolve b0e156 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e156
      have b0e158 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e157
           have i₂ := b0e114
           grind)
        | exact superpose b0e114 b0e157
        | exact resolve b0e157 b0e114
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e114 b0e157
      have b0e159 : False := by grind
      exact b0e159
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op X1 X1) ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op (M.op x x) x) = (M.op y y) := by grind
        have b1e21 : (M.op (M.op (σ x) (σ x)) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (M.op (σ x) (σ x)) ≠ (M.op (M.op (σ x) (σ x)) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e25 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e19
          | exact resolve b1e19 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e26 : y = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 y
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e13
          | exact resolve b1e13 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e27 : x = y := by
          first
          | (have i₁ := b1e26
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e26
          | exact resolve b1e26 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e38 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op y y) ∨ (k x X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b1e15 x X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e15
          | (have j0 := b1e15 x X0
             grind)
          | (have r₁ := b1e15 x y
             have r₂ := b1e20
             grind)
          | exact resolve b1e15 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e39 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k x X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b1e38 X0
             have i₂ := b1e27
             grind)
          | exact superpose b1e27 b1e38
          | (have j0 := b1e38 X0
             grind)
          | exact resolve b1e38 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38
        have b1e50 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by grind
        clear b1e24
        have b1e52 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by grind
        clear b1e50
        have b1e53 : (M.op (σ x) (σ x)) = (σ (k x x)) := by
          first
          | (have i₁ := b1e52
             have i₂ := b1e18 x x
             grind)
          | exact superpose b1e18 b1e52
          | exact resolve b1e52 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52
        have b1e55 : (σ (M.op x y)) ≠ (σ (k x x)) := by
          first
          | (have i₁ := b1e25
             have i₂ := b1e53
             grind)
          | exact superpose b1e53 b1e25
          | exact resolve b1e25 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e53
        have b1e58 : (σ (k x x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e55
             have i₂ := b1e27
             grind)
          | exact superpose b1e27 b1e55
          | exact resolve b1e55 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27 b1e55
        have b1e102 : (M.op x x) = (k x x) := by
          first
          | (have j0 := b1e39 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39
        have b1e104 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e58
             have i₂ := b1e102
             grind)
          | exact superpose b1e102 b1e58
          | exact resolve b1e58 b1e102
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e58 b1e102
        have b1e105 : False := by grind
        exact b1e105
      · have b2e15 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op (M.op x x) x) = (M.op y y) := by grind
        have b2e22 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e38 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op y y) ∨ (k x X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b2e15 x X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e15
          | (have j0 := b2e15 x X0
             grind)
          | (have r₁ := b2e15 x y
             have r₂ := b2e20
             grind)
          | exact resolve b2e15 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e58 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X1 X1) X1) ∨ (k X1 X2) = (M.op X1 X2) ∨ X1 = X2 ∨ (k X0 X2) = (M.op X0 X2) ∨ X0 = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e17 X0 X2
             have i₂ := b2e17 X1 X2
             grind)
          | exact superpose b2e17 b2e17
          | (have j0 := b2e17 X1 X2
             have j1 := b2e17 X1 X2
             grind)
          | exact resolve b2e17 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e65 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X1 X1) X1) ∨ (k X1 X2) = (M.op X1 X2) ∨ (k X0 X2) = (M.op X0 X2) ∨ X0 = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 X1 X2
             have i₂ := b2e17 X0 X2
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X1 X2
             have j1 := b2e17 X0 X2
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 (M.op (M.op X0 X0) X0) (M.op X1 X1)
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 (M.op X1 X1) (M.op (M.op X0 X0) X0)
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e73 : ∀ X0 X1 X2 : G, (k X1 X2) = (M.op X1 X2) ∨ (k X0 X2) = (M.op X0 X2) ∨ X1 = X2 ∨ X0 = X2 := by
          intro X0 X1 X2
          first
          | (have j0 := b2e58 X1 X1 X2
             have j1 := b2e65 X1 X1 X2
             grind)
          | (have r₁ := b2e58 X0 X1 X2
             have r₂ := b2e65 X0 X1 X2
             grind)
          | (have r₁ := b2e58 X1 X0 X2
             have r₂ := b2e65 X0 X1 X2
             grind)
          | (have r₁ := b2e58 X0 (M.op (M.op X0 X0) X0) (M.op (M.op X1 X1) X1)
             have r₂ := b2e65 X0 X1 X2
             grind)
          | exact resolve b2e58 b2e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e58 b2e65
        have b2e81 : (M.op x y) = (k x y) := by
          first
          | (have j0 := b2e38 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38
        have b2e130 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e73 X0 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e73
        have b2e131 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e130 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e130
        have b2e132 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e131 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e131
        have b2e138 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e132 (σ X0) (σ X1)
             grind)
          | exact superpose b2e132 b2e18
          | (have j1 := b2e132 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
             grind)
          | exact resolve b2e18 b2e132
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e132
        have b2e1789 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e138 x y
             grind)
          | exact superpose b2e138 b2e19
          | (have j1 := b2e138 x y
             grind)
          | exact resolve b2e19 b2e138
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e138
        have b2e1796 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e1789
             have r₂ := b2e22
             grind)
          | exact resolve b2e1789 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1789
        have b2e1799 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b2e1796
             have i₂ := b2e81
             grind)
          | exact superpose b2e81 b2e1796
          | exact resolve b2e1796 b2e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e81 b2e1796
        have b2e1800 : False := by grind
        exact b2e1800
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op X1 X1) ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : (M.op (M.op x x) x) ≠ (M.op y y) := by grind
        have b3e21 : x = y := by grind
        have b3e22 : (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e33 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ y) (σ y)) ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
          intro X0
          grind
        have b3e42 : (M.op y y) ≠ (M.op y y) ∨ (M.op y y) = (k y y) := by grind
        have b3e44 : (M.op y y) = (k y y) := by grind
        clear b3e42
        have b3e145 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
          first
          | (have j0 := b3e33 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33
        have b3e146 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e145
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e145
          | exact resolve b3e145 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e145
        have b3e147 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e146
             have i₂ := b3e44
             grind)
          | exact superpose b3e44 b3e146
          | exact resolve b3e146 b3e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44 b3e146
        have b3e148 : False := by grind
        exact b3e148
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e17 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op X1 X1) ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : (M.op (M.op x x) x) ≠ (M.op y y) := by grind
          have b4e22 : x = y := by grind
          have b4e23 : (M.op (M.op (σ x) (σ x)) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e44 : (M.op y y) ≠ (M.op y y) ∨ (M.op y y) = (k y y) := by grind
          have b4e45 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by grind
          have b4e47 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b4e45
          have b4e48 : (M.op y y) = (k y y) := by grind
          clear b4e44
          have b4e49 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b4e47
               have i₂ := b4e19 y y
               grind)
            | exact superpose b4e19 b4e47
            | exact resolve b4e47 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e47
          have b4e50 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e49
               have i₂ := b4e48
               grind)
            | exact superpose b4e48 b4e49
            | exact resolve b4e49 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48 b4e49
          have b4e51 : False := by grind
          exact b4e51
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : (M.op (M.op x x) x) ≠ (M.op y y) := by grind
        have b6e21 : x ≠ y := by grind
        have b6e22 : (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e38 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ y) (σ y)) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b6e15 (σ x) X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e15
          | (have j0 := b6e15 (σ x) X0
             grind)
          | (have r₁ := b6e15 (σ x) (σ y)
             have r₂ := b6e22
             grind)
          | exact resolve b6e15 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e65 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op y y) ∨ (k x X0) = (M.op x X0) ∨ x = X0 := by
          intro X0
          first
          | (have i₁ := b6e20
             have i₂ := b6e17 x X0
             grind)
          | exact superpose b6e17 b6e20
          | (have j1 := b6e17 x X0
             grind)
          | (have r₁ := b6e20
             have r₂ := b6e17 x y
             grind)
          | (have r₁ := b6e20
             have r₂ := b6e17 (M.op (M.op x x) x) (M.op y y)
             grind)
          | (have r₁ := b6e20
             have r₂ := b6e17 (M.op y y) (M.op (M.op x x) x)
             grind)
          | exact resolve b6e20 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e117 : (M.op x y) = (k x y) ∨ x = y := by
          first
          | (have j0 := b6e65 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e65
        have b6e118 : (M.op x y) = (k x y) := by
          first
          | (have r₁ := b6e117
             have r₂ := b6e21
             grind)
          | exact resolve b6e117 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e117
        have b6e155 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b6e38 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38
        have b6e156 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e155
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e155
          | exact resolve b6e155 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e155
        have b6e157 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e156
             have i₂ := b6e118
             grind)
          | exact superpose b6e118 b6e156
          | exact resolve b6e156 b6e118
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e118 b6e156
        have b6e158 : False := by grind
        exact b6e158
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e22 : x ≠ y := by grind
          have b7e24 : (σ x) = (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e28 : y = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 y
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e14
            | exact resolve b7e14 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e29 : x = y := by
            first
            | (have i₁ := b7e28
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e28
            | exact resolve b7e28 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28
          have b7e30 : False := by grind
          exact b7e30
        · have b8e16 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : (M.op (M.op x x) x) ≠ (M.op y y) := by grind
          have b8e22 : x ≠ y := by grind
          have b8e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e55 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X1 X1) X1) ∨ (k X1 X2) = (M.op X1 X2) ∨ X1 = X2 ∨ (k X0 X2) = (M.op X0 X2) ∨ X0 = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e18 X0 X2
               have i₂ := b8e18 X1 X2
               grind)
            | exact superpose b8e18 b8e18
            | (have j0 := b8e18 X1 X2
               have j1 := b8e18 X1 X2
               grind)
            | exact resolve b8e18 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e57 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op y y) ∨ (k x X0) = (M.op x X0) ∨ x = X0 := by
            intro X0
            first
            | (have i₁ := b8e21
               have i₂ := b8e18 x X0
               grind)
            | exact superpose b8e18 b8e21
            | (have j1 := b8e18 x X0
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e18 x y
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e18 (M.op (M.op x x) x) (M.op y y)
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e18 (M.op y y) (M.op (M.op x x) x)
               grind)
            | exact resolve b8e21 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e62 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X1 X1) X1) ∨ (k X1 X2) = (M.op X1 X2) ∨ (k X0 X2) = (M.op X0 X2) ∨ X0 = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e16 X1 X2
               have i₂ := b8e18 X0 X2
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X1 X2
               have j1 := b8e18 X0 X2
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 (M.op (M.op X0 X0) X0) (M.op X1 X1)
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 (M.op X1 X1) (M.op (M.op X0 X0) X0)
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e69 : ∀ X0 X1 X2 : G, (k X1 X2) = (M.op X1 X2) ∨ (k X0 X2) = (M.op X0 X2) ∨ X1 = X2 ∨ X0 = X2 := by
            intro X0 X1 X2
            first
            | (have j0 := b8e55 X1 X1 X2
               have j1 := b8e62 X1 X1 X2
               grind)
            | (have r₁ := b8e55 X0 X1 X2
               have r₂ := b8e62 X0 X1 X2
               grind)
            | (have r₁ := b8e55 X1 X0 X2
               have r₂ := b8e62 X0 X1 X2
               grind)
            | (have r₁ := b8e55 X0 (M.op (M.op X0 X0) X0) (M.op (M.op X1 X1) X1)
               have r₂ := b8e62 X0 X1 X2
               grind)
            | exact resolve b8e55 b8e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55 b8e62
          have b8e99 : (M.op x y) = (k x y) ∨ x = y := by
            first
            | (have j0 := b8e57 y
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e57
          have b8e100 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b8e99
               have r₂ := b8e22
               grind)
            | exact resolve b8e99 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e99
          have b8e174 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e69 X0 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e69
          have b8e175 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e174 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e174
          have b8e176 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e175 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e175
          have b8e185 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e176 (σ X0) (σ X1)
               grind)
            | exact superpose b8e176 b8e19
            | (have j1 := b8e176 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
               grind)
            | exact resolve b8e19 b8e176
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e176
          have b8e1381 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e185 x y
               grind)
            | exact superpose b8e185 b8e20
            | (have j1 := b8e185 x y
               grind)
            | exact resolve b8e20 b8e185
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e185
          have b8e1388 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e1381
               have r₂ := b8e24
               grind)
            | exact resolve b8e1381 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1381
          have b8e1391 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b8e1388
               have i₂ := b8e100
               grind)
            | exact superpose b8e100 b8e1388
            | exact resolve b8e1388 b8e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e100 b8e1388
          have b8e1392 : False := by grind
          exact b8e1392

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(X,X),Y) = m(X,Y) then m(Y,X) else if m(X,X) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppxxy_pxy_pxx_x_pyx_pyy_pyx_Equation1 :
    AutBox.GuardAut2 (((Lf 0) ⋆ (Lf 0)) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 0) ⋆ (Lf 0)) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op a a) b ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) b) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op a a) b = M.op a b ∨ M.op a a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) b) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op a a) b = M.op a b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) b) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op x x) y) (M.op x y) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (σ y)) (M.op (σ x) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e42 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 X0 X1
           have i₂ := b0e16 X0 X1
           grind)
        | exact superpose b0e16 b0e14
        | (have j0 := b0e14 X0 X1
           have j1 := b0e16 X0 X1
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | exact resolve b0e14 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e45 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e42 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42
      have b0e46 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e45 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45
      have b0e52 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X2) = (M.op X2 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e14 X0 X1
           have i₂ := b0e46 X0 X2
           grind)
        | exact superpose b0e46 b0e14
        | (have j0 := b0e14 X0 X1
           have j1 := b0e46 X0 X1
           grind)
        | exact resolve b0e14 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46
      have b0e55 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X2) = (M.op X2 X0) := by
        intro X0 X1 X2
        first
        | (have j0 := b0e52 X0 X1 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e52
      have b0e112 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e55 X0 X1 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e55
      have b0e113 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e112 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e112
      have b0e119 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X1 X0
           have i₂ := b0e113 (σ X1) (σ X0)
           grind)
        | exact superpose b0e113 b0e17
        | exact resolve b0e17 b0e113
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e126 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e119 X0 X1
           have i₂ := b0e113 X1 X0
           grind)
        | exact superpose b0e113 b0e119
        | exact resolve b0e119 b0e113
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e113 b0e119
      have b0e716 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e126 x y
           grind)
        | exact superpose b0e126 b0e18
        | (have r₁ := b0e18
           have r₂ := b0e126 x y
           grind)
        | exact resolve b0e18 b0e126
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e126
      have b0e725 : False := by grind
      exact b0e725
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
      · have b1e21 : (M.op (σ x) (σ y)) ≠ (M.op (M.op (σ x) (σ x)) (σ y)) := by grind
        have b1e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e24 : False := by grind
        exact b1e24
      · have b2e15 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e49 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X0 X1
             have i₂ := b2e17 X0 X1
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X0 X1
             have j1 := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e52 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e49 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e49
        have b2e53 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e52 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52
        have b2e74 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X2) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 X0 X1
             have i₂ := b2e53 X0 X2
             grind)
          | exact superpose b2e53 b2e15
          | (have j0 := b2e15 X0 X1
             have j1 := b2e53 X0 X1
             grind)
          | exact resolve b2e15 b2e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53
        have b2e81 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X2) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b2e74 X0 X1 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e74
        have b2e137 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e81 X0 X1 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e81
        have b2e138 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e137 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e137
        have b2e144 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e138 (σ X1) (σ X0)
             grind)
          | exact superpose b2e138 b2e18
          | exact resolve b2e18 b2e138
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e151 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e144 X0 X1
             have i₂ := b2e138 X1 X0
             grind)
          | exact superpose b2e138 b2e144
          | exact resolve b2e144 b2e138
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e138 b2e144
        have b2e1175 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e151 x y
             grind)
          | exact superpose b2e151 b2e19
          | (have r₁ := b2e19
             have r₂ := b2e151 x y
             grind)
          | exact resolve b2e19 b2e151
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e151
        have b2e1188 : False := by grind
        exact b2e1188
  · rcases eq_or_ne (M.op x x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (σ y)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e20 : (M.op x y) ≠ (M.op (M.op x x) y) := by grind
        have b3e21 : x = (M.op x x) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : (M.op x y) ≠ (M.op x y) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e20
          | exact resolve b3e20 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e24 : False := by grind
        exact b3e24
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b4e23 : (M.op (σ x) (σ y)) ≠ (M.op (M.op (σ x) (σ x)) (σ y)) := by grind
          have b4e24 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e25 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e23
            | exact resolve b4e23 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e26 : False := by grind
          exact b4e26
        · have b5e21 : (M.op x y) ≠ (M.op (M.op x x) y) := by grind
          have b5e22 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : (M.op x y) ≠ (M.op x y) := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e21
            | exact resolve b5e21 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e26 : False := by grind
          exact b5e26
    · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (σ y)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x y) ≠ (M.op (M.op x x) y) := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e23 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b6e24 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X1 (τ X0)
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e18
          | exact resolve b6e18 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b6e13 (k (τ X0) X1)
             have i₂ := b6e23 X0 X1
             grind)
          | exact superpose b6e23 b6e13
          | exact resolve b6e13 b6e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23
        have b6e34 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e13 (k X0 (τ X1))
             have i₂ := b6e24 X1 X0
             grind)
          | exact superpose b6e24 b6e13
          | exact resolve b6e13 b6e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24
        have b6e50 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e15 X0 X1
             have i₂ := b6e17 X0 X1
             grind)
          | exact superpose b6e17 b6e15
          | (have j0 := b6e15 X0 X1
             have j1 := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e53 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e50 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e50
        have b6e54 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e53 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e53
        have b6e75 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X2) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e15 X0 X1
             have i₂ := b6e54 X0 X2
             grind)
          | exact superpose b6e54 b6e15
          | (have j0 := b6e15 X0 X1
             have j1 := b6e54 X0 X1
             grind)
          | exact resolve b6e15 b6e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e54
        have b6e78 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X2) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b6e75 X0 X1 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e75
        have b6e111 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e78 X0 X1 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e78
        have b6e112 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e111 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e111
        have b6e119 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b6e34 X1 X0
             have i₂ := b6e112 (σ X1) X0
             grind)
          | exact superpose b6e112 b6e34
          | exact resolve b6e34 b6e112
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e34
        have b6e123 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e28 X1 X0
             have i₂ := b6e112 X1 (σ X0)
             grind)
          | exact superpose b6e112 b6e28
          | exact resolve b6e28 b6e112
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28
        have b6e124 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e123 X0 X1
             have i₂ := b6e112 (τ X1) X0
             grind)
          | exact superpose b6e112 b6e123
          | exact resolve b6e123 b6e112
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e123
        have b6e128 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (M.op (τ X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e119 X0 X1
             have i₂ := b6e112 X1 (τ X0)
             grind)
          | exact superpose b6e112 b6e119
          | exact resolve b6e119 b6e112
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e112 b6e119
        have b6e912 : (M.op (τ (M.op (σ x) (σ x))) y) = (τ (M.op (σ x) (σ y))) := by
          first
          | (have i₁ := b6e128 (M.op (σ x) (σ x)) y
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e128
          | exact resolve b6e128 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e128
        have b6e938 : (M.op (τ (M.op (σ x) (σ x))) y) = (M.op x (τ (σ y))) := by
          first
          | (have i₁ := b6e912
             have i₂ := b6e124 x (σ y)
             grind)
          | exact superpose b6e124 b6e912
          | exact resolve b6e912 b6e124
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e912
        have b6e948 : (M.op x y) = (M.op (τ (M.op (σ x) (σ x))) y) := by
          first
          | (have i₁ := b6e938
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e938
          | exact resolve b6e938 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e938
        have b6e951 : (M.op x y) = (M.op (M.op x (τ (σ x))) y) := by
          first
          | (have i₁ := b6e948
             have i₂ := b6e124 x (σ x)
             grind)
          | exact superpose b6e124 b6e948
          | exact resolve b6e948 b6e124
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e124 b6e948
        have b6e952 : (M.op x y) = (M.op (M.op x x) y) := by
          first
          | (have i₁ := b6e951
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e951
          | exact resolve b6e951 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e951
        have b6e953 : False := by grind
        exact b6e953
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b7e23 : (M.op (σ x) (σ y)) ≠ (M.op (M.op (σ x) (σ x)) (σ y)) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e26 : False := by grind
          exact b7e26
        · have b8e16 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e50 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X0 X1
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X0 X1
               have j1 := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e53 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e50 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e50
          have b8e54 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e53 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e53
          have b8e76 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X2) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e16 X0 X1
               have i₂ := b8e54 X0 X2
               grind)
            | exact superpose b8e54 b8e16
            | (have j0 := b8e16 X0 X1
               have j1 := b8e54 X0 X1
               grind)
            | exact resolve b8e16 b8e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e54
          have b8e83 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X2) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b8e76 X0 X1 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e76
          have b8e139 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e83 X0 X1 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e83
          have b8e140 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e139 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e139
          have b8e144 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e140 (σ X1) (σ X0)
               grind)
            | exact superpose b8e140 b8e19
            | exact resolve b8e19 b8e140
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e155 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e144 X0 X1
               have i₂ := b8e140 X1 X0
               grind)
            | exact superpose b8e140 b8e144
            | exact resolve b8e144 b8e140
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e140 b8e144
          have b8e1473 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e155 x y
               grind)
            | exact superpose b8e155 b8e20
            | (have r₁ := b8e20
               have r₂ := b8e155 x y
               grind)
            | exact resolve b8e20 b8e155
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e155
          have b8e1488 : False := by grind
          exact b8e1488

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(X,X),Y) = m(Y,m(Y,Y)) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppxxy_pypyy_pxy_y_pxy_y_pxy_Equation1 :
    AutBox.GuardAut2 (((Lf 0) ⋆ (Lf 0)) ⋆ (Lf 1)) ((Lf 1) ⋆ ((Lf 1) ⋆ (Lf 1))) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 0) ⋆ (Lf 0)) ⋆ (Lf 1)) ((Lf 1) ⋆ ((Lf 1) ⋆ (Lf 1))) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op a a) b ≠ M.op b (M.op b b) ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) b) (M.op b (M.op b b))).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op a a) b = M.op b (M.op b b) ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) b) (M.op b (M.op b b))).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op a a) b = M.op b (M.op b b) ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op a a) b) (M.op b (M.op b b))).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op x x) y) (M.op y (M.op y y)) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (σ y)) (M.op (σ y) (M.op (σ y) (σ y))) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ (M.op X1 (M.op X1 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op (M.op x x) y) = (M.op y (M.op y y)) := by grind
      have b0e20 : (M.op (M.op (σ x) (σ x)) (σ y)) = (M.op (σ y) (M.op (σ y) (σ y))) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e43 : (M.op y (M.op y y)) ≠ (M.op y (M.op y y)) ∨ (M.op x y) = (k x y) := by
        first
        | (have i₁ := b0e14 x y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 x y
           grind)
        | (have r₁ := b0e14 x y
           have r₂ := b0e19
           grind)
        | exact resolve b0e14 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e44 : (M.op (σ y) (M.op (σ y) (σ y))) ≠ (M.op (σ y) (M.op (σ y) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have i₁ := b0e14 (σ x) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have j0 := b0e14 (σ x) (σ y)
           grind)
        | (have r₁ := b0e14 (σ x) (σ y)
           have r₂ := b0e20
           grind)
        | exact resolve b0e14 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e45 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
      clear b0e44
      have b0e46 : (M.op x y) = (k x y) := by grind
      clear b0e43
      have b0e47 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e45
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e45
        | exact resolve b0e45 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45
      have b0e48 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e47
           have i₂ := b0e46
           grind)
        | exact superpose b0e46 b0e47
        | exact resolve b0e47 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46 b0e47
      have b0e49 : False := by grind
      exact b0e49
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ (M.op X1 (M.op X1 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op (M.op X0 X0) X1) = (M.op X1 (M.op X1 X1)) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op (M.op x x) y) = (M.op y (M.op y y)) := by grind
        have b1e21 : (M.op (M.op (σ x) (σ x)) (σ y)) ≠ (M.op (σ y) (M.op (σ y) (σ y))) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e19
          | exact resolve b1e19 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e38 : (M.op y (M.op y y)) ≠ (M.op y (M.op y y)) ∨ (M.op x y) = (k x y) := by
          first
          | (have i₁ := b1e15 x y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e15
          | (have j0 := b1e15 x y
             grind)
          | (have r₁ := b1e15 x y
             have r₂ := b1e20
             grind)
          | exact resolve b1e15 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e39 : (M.op x y) = (k x y) := by grind
        clear b1e38
        have b1e40 : (σ y) ≠ (σ y) ∨ (M.op (M.op (σ x) (σ x)) (σ y)) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e42 : (M.op (M.op (σ x) (σ x)) (σ y)) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e40
        have b1e43 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e42
             have r₂ := b1e21
             grind)
          | exact resolve b1e42 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42
        have b1e44 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e43
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e43
          | exact resolve b1e43 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43
        have b1e45 : (σ (M.op x y)) = (σ y) := by
          first
          | (have i₁ := b1e44
             have i₂ := b1e39
             grind)
          | exact superpose b1e39 b1e44
          | exact resolve b1e44 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39 b1e44
        have b1e46 : False := by grind
        exact b1e46
      · have b2e15 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ (M.op X1 (M.op X1 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X1 (M.op X1 X1)) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op (M.op x x) y) = (M.op y (M.op y y)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e37 : (M.op y (M.op y y)) ≠ (M.op y (M.op y y)) ∨ (M.op x y) = (k x y) := by
          first
          | (have i₁ := b2e15 x y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e15
          | (have j0 := b2e15 x y
             grind)
          | (have r₁ := b2e15 x y
             have r₂ := b2e20
             grind)
          | exact resolve b2e15 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e38 : (M.op x y) = (k x y) := by grind
        clear b2e37
        have b2e50 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X1 X0
             have i₂ := b2e17 X1 X0
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X1 X0
             have j1 := b2e17 X1 X0
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X0 (M.op X0 X0)
             have r₂ := b2e17 (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e54 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e50 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50
        have b2e55 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e54 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e54
        have b2e72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e55 (σ X1) (σ X0)
             grind)
          | exact superpose b2e55 b2e18
          | (have j1 := b2e55 (σ X1) (σ X0)
             grind)
          | exact resolve b2e18 b2e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55
        have b2e325 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e72 x y
             grind)
          | exact superpose b2e72 b2e19
          | (have j1 := b2e72 x y
             grind)
          | exact resolve b2e19 b2e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e72
        have b2e340 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e325
             have r₂ := b2e22
             grind)
          | exact resolve b2e325 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e325
        have b2e344 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b2e340
             have i₂ := b2e38
             grind)
          | exact superpose b2e38 b2e340
          | exact resolve b2e340 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38 b2e340
        have b2e345 : False := by grind
        exact b2e345
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (σ y)) (M.op (σ y) (M.op (σ y) (σ y))) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ (M.op X1 (M.op X1 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op (M.op X0 X0) X1) = (M.op X1 (M.op X1 X1)) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : (M.op (M.op x x) y) ≠ (M.op y (M.op y y)) := by grind
        have b3e21 : y = (M.op x y) := by grind
        have b3e22 : (M.op (M.op (σ x) (σ x)) (σ y)) = (M.op (σ y) (M.op (σ y) (σ y))) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e19
          | exact resolve b3e19 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e38 : (M.op (σ y) (M.op (σ y) (σ y))) ≠ (M.op (σ y) (M.op (σ y) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b3e15 (σ x) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e15
          | (have j0 := b3e15 (σ x) (σ y)
             grind)
          | (have r₁ := b3e15 (σ x) (σ y)
             have r₂ := b3e22
             grind)
          | exact resolve b3e15 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e39 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b3e38
        have b3e40 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e39
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e39
          | exact resolve b3e39 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39
        have b3e41 : (σ y) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e40
             grind)
          | exact superpose b3e40 b3e23
          | exact resolve b3e23 b3e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e40
        have b3e42 : y ≠ y ∨ (M.op (M.op x x) y) = (M.op y (M.op y y)) ∨ y = (k x y) := by
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
        have b3e45 : (M.op (M.op x x) y) = (M.op y (M.op y y)) ∨ y = (k x y) := by grind
        clear b3e42
        have b3e46 : y = (k x y) := by
          first
          | (have r₁ := b3e45
             have r₂ := b3e20
             grind)
          | exact resolve b3e45 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45
        have b3e56 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b3e41
             have i₂ := b3e46
             grind)
          | exact superpose b3e46 b3e41
          | exact resolve b3e41 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e41 b3e46
        have b3e57 : False := by grind
        exact b3e57
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x y) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e25 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e26 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e25
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e25
            | exact resolve b4e25 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25
          have b4e27 : False := by grind
          exact b4e27
        · have b5e16 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ (M.op X1 (M.op X1 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op (M.op X0 X0) X1) = (M.op X1 (M.op X1 X1)) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X1 (M.op X1 X1)) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op (M.op x x) y) ≠ (M.op y (M.op y y)) := by grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e48 : y ≠ y ∨ (M.op (M.op x x) y) = (M.op y (M.op y y)) ∨ y = (k x y) := by
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
          have b5e49 : (M.op (M.op x x) y) = (M.op y (M.op y y)) ∨ y = (k x y) := by grind
          clear b5e48
          have b5e50 : y = (k x y) := by
            first
            | (have r₁ := b5e49
               have r₂ := b5e21
               grind)
            | exact resolve b5e49 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49
          have b5e54 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e16 X1 X0
               have i₂ := b5e18 X1 X0
               grind)
            | exact superpose b5e18 b5e16
            | (have j0 := b5e16 X1 X0
               have j1 := b5e18 X1 X0
               grind)
            | (have r₁ := b5e16 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | (have r₁ := b5e16 X0 (M.op X0 X0)
               have r₂ := b5e18 (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))
               grind)
            | exact resolve b5e16 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e58 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e54 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e54
          have b5e59 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e58 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58
          have b5e78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X0 X1
               have i₂ := b5e59 (σ X1) (σ X0)
               grind)
            | exact superpose b5e59 b5e19
            | (have j1 := b5e59 (σ X1) (σ X0)
               grind)
            | exact resolve b5e19 b5e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59
          have b5e382 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e78 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e78
          have b5e482 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e382 x y
               have i₂ := b5e50
               grind)
            | exact superpose b5e50 b5e382
            | (have j0 := b5e382 x y
               grind)
            | exact resolve b5e382 b5e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50 b5e382
          have b5e486 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b5e482
          have b5e489 : False := by grind
          exact b5e489
    · rcases eq_or_ne (M.op (M.op (σ x) (σ x)) (σ y)) (M.op (σ y) (M.op (σ y) (σ y))) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ (M.op X1 (M.op X1 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X1 (M.op X1 X1)) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e21 : y ≠ (M.op x y) := by grind
        have b6e22 : (M.op (M.op (σ x) (σ x)) (σ y)) = (M.op (σ y) (M.op (σ y) (σ y))) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e37 : (M.op (σ y) (M.op (σ y) (σ y))) ≠ (M.op (σ y) (M.op (σ y) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e15
          | (have j0 := b6e15 (σ x) (σ y)
             grind)
          | (have r₁ := b6e15 (σ x) (σ y)
             have r₂ := b6e22
             grind)
          | exact resolve b6e15 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e38 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b6e37
        have b6e39 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e38
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e38
          | exact resolve b6e38 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38
        have b6e40 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e39
             grind)
          | exact superpose b6e39 b6e19
          | exact resolve b6e19 b6e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39
        have b6e45 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e15 X1 X0
             have i₂ := b6e17 X1 X0
             grind)
          | exact superpose b6e17 b6e15
          | (have j0 := b6e15 X1 X0
             have j1 := b6e17 X1 X0
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X0 (M.op X0 X0)
             have r₂ := b6e17 (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e49 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e45 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e45
        have b6e50 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e49 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e49
        have b6e65 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e40
             have i₂ := b6e50 y x
             grind)
          | exact superpose b6e50 b6e40
          | (have j1 := b6e50 y x
             grind)
          | exact resolve b6e40 b6e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40 b6e50
        have b6e66 : y = (M.op x y) := by grind
        clear b6e65
        have b6e67 : False := by grind
        exact b6e67
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ (M.op X1 (M.op X1 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op (M.op X0 X0) X1) = (M.op X1 (M.op X1 X1)) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X1 (M.op X1 X1)) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (M.op (M.op (σ x) (σ x)) (σ y)) ≠ (M.op (σ y) (M.op (σ y) (σ y))) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e60 : (σ y) ≠ (σ y) ∨ (M.op (M.op (σ x) (σ x)) (σ y)) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e61 : (M.op (M.op (σ x) (σ x)) (σ y)) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e60
          have b7e62 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e61
               have r₂ := b7e23
               grind)
            | exact resolve b7e61 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e63 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e62
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e62
            | exact resolve b7e62 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e68 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e63
               grind)
            | exact superpose b7e63 b7e14
            | exact resolve b7e14 b7e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63
          have b7e69 : y = (k x y) := by
            first
            | (have i₁ := b7e68
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e68
            | exact resolve b7e68 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e77 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e16 X1 X0
               have i₂ := b7e18 X1 X0
               grind)
            | exact superpose b7e18 b7e16
            | (have j0 := b7e16 X1 X0
               have j1 := b7e18 X1 X0
               grind)
            | (have r₁ := b7e16 X0 X1
               have r₂ := b7e18 X0 X1
               grind)
            | (have r₁ := b7e16 X0 (M.op X0 X0)
               have r₂ := b7e18 (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))
               grind)
            | exact resolve b7e16 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e81 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e77 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77
          have b7e82 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e81 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e81
          have b7e92 : y = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e69
               have i₂ := b7e82 y x
               grind)
            | exact superpose b7e82 b7e69
            | (have j1 := b7e82 y x
               grind)
            | exact resolve b7e69 b7e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69 b7e82
          have b7e94 : y = (M.op x y) := by grind
          clear b7e92
          have b7e97 : False := by grind
          exact b7e97
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ (M.op X1 (M.op X1 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X1 (M.op X1 X1)) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : y ≠ (M.op x y) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
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
          have b8e72 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X1 X0
               have i₂ := b8e18 X1 X0
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X1 X0
               have j1 := b8e18 X1 X0
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 (M.op X0 X0)
               have r₂ := b8e18 (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e76 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e72 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72
          have b8e77 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e76 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e76
          have b8e82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e77 (σ X1) (σ X0)
               grind)
            | exact superpose b8e77 b8e19
            | (have j1 := b8e77 (σ X1) (σ X0)
               grind)
            | exact resolve b8e19 b8e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e84 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e25 X0 X1
               have i₂ := b8e77 X1 (τ X0)
               grind)
            | exact superpose b8e77 b8e25
            | (have j1 := b8e77 X1 (τ X0)
               grind)
            | exact resolve b8e25 b8e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25 b8e77
          have b8e212 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e84 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e84
            | exact resolve b8e84 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e84
          have b8e238 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e212 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e212
            | (have j0 := b8e212 X0 X1
               grind)
            | exact resolve b8e212 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e212
          have b8e361 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e82 x y
               grind)
            | exact superpose b8e82 b8e20
            | (have j1 := b8e82 x y
               grind)
            | exact resolve b8e20 b8e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e82
          have b8e376 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e361
               have r₂ := b8e24
               grind)
            | exact resolve b8e361 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e361
          have b8e381 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e376
               have i₂ := b8e238 x y
               grind)
            | exact superpose b8e238 b8e376
            | (have j1 := b8e238 x y
               grind)
            | (have r₁ := b8e376
               have r₂ := b8e238 x y
               grind)
            | exact resolve b8e376 b8e238
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e238 b8e376
          have b8e382 : y = (M.op x y) := by grind
          clear b8e381
          have b8e384 : False := by grind
          exact b8e384

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(X,Y),m(X,X)) = m(Y,X) then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppxypxx_pyx_x_y_pyx_pxx_pyx_Equation1 :
    AutBox.GuardAut2 (((Lf 0) ⋆ (Lf 1)) ⋆ ((Lf 0) ⋆ (Lf 0))) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 0) ⋆ (Lf 1)) ⋆ ((Lf 0) ⋆ (Lf 0))) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op a b) (M.op a a) ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a b) (M.op a a)) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op a b) (M.op a a) = M.op b a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a b) (M.op a a)) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op a b) (M.op a a) = M.op b a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a b) (M.op a a)) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op x y) (M.op x x)) (M.op y x) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) (M.op (σ y) (σ x)) with h1a | h1a
    · have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = (M.op X1 X0) ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e23 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X1 (τ X0)
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e17
        | exact resolve b0e17 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e53 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        grind
      have b0e56 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e53 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e53
      have b0e57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e56 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e56
      have b0e61 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e57 (σ X0)
           grind)
        | exact superpose b0e57 b0e17
        | exact resolve b0e17 b0e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e64 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e61 X0
           have i₂ := b0e57 X0
           grind)
        | exact superpose b0e57 b0e61
        | exact resolve b0e61 b0e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e57 b0e61
      have b0e76 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 X1 X0
           have i₂ := b0e16 X1 X0
           grind)
        | exact superpose b0e16 b0e14
        | (have j0 := b0e14 X1 X0
           have j1 := b0e16 (M.op X0 X1) (k X1 X0)
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 (M.op (M.op X0 X1) (M.op X0 X0)) (M.op X1 X0)
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 (M.op X1 X0) (M.op (M.op X0 X1) (M.op X0 X0))
           grind)
        | exact resolve b0e14 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e78 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e76 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e76
      have b0e79 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e78 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e78
      have b0e88 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e23 X0 X1
           have i₂ := b0e79 (τ X0) X1
           grind)
        | exact superpose b0e79 b0e23
        | (have j1 := b0e79 (k (σ X1) X0) (σ (M.op (τ X0) X1))
           grind)
        | exact resolve b0e23 b0e79
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23
      have b0e89 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X1 X0
           have i₂ := b0e79 (σ X0) (σ X1)
           grind)
        | exact superpose b0e79 b0e17
        | (have j1 := b0e79 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
           grind)
        | exact resolve b0e17 b0e79
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e79
      have b0e195 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e88 (σ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e88
        | exact resolve b0e88 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e88
      have b0e211 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e195 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e195
        | (have j0 := b0e195 (σ (k X1 X0)) (σ (M.op X0 X1))
           grind)
        | exact resolve b0e195 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e195
      have b0e516 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e89 x y
           grind)
        | exact superpose b0e89 b0e18
        | (have j1 := b0e89 x y
           grind)
        | exact resolve b0e18 b0e89
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e89
      have b0e549 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
        first
        | (have i₁ := b0e516
           have i₂ := b0e211 x y
           grind)
        | exact superpose b0e211 b0e516
        | (have j1 := b0e211 (σ x) (σ y)
           grind)
        | (have r₁ := b0e516
           have r₂ := b0e211 x y
           grind)
        | (have r₁ := b0e516
           have r₂ := b0e211 (σ (M.op x y)) (σ (k y x))
           grind)
        | (have r₁ := b0e516
           have r₂ := b0e211 (σ (k y x)) (σ (M.op x y))
           grind)
        | exact resolve b0e516 b0e211
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e211 b0e516
      have b0e550 : (σ x) = (σ y) ∨ x = y := by grind
      clear b0e549
      have b0e557 : y = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b0e12 y
           have i₂ := b0e550
           grind)
        | exact superpose b0e550 b0e12
        | exact resolve b0e12 b0e550
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e550
      have b0e588 : x = y ∨ x = y := by
        first
        | (have i₁ := b0e557
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e557
        | exact resolve b0e557 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e557
      have b0e589 : x = y := by grind
      clear b0e588
      have b0e603 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e589
           grind)
        | exact superpose b0e589 b0e18
        | exact resolve b0e18 b0e589
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e589
      have b0e615 : False := by grind
      exact b0e615
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = (M.op X1 X0) ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e25 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e19
          | exact resolve b1e19 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e26 : y = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 y
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e13
          | exact resolve b1e13 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e27 : x = y := by
          first
          | (have i₁ := b1e26
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e26
          | exact resolve b1e26 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e68 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          grind
        have b1e71 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e68 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e68
        have b1e72 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e71 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e71
        have b1e77 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e72 (σ X0)
             grind)
          | exact superpose b1e72 b1e18
          | exact resolve b1e18 b1e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e80 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e77 X0
             have i₂ := b1e72 X0
             grind)
          | exact superpose b1e72 b1e77
          | exact resolve b1e77 b1e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e72 b1e77
        have b1e129 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e25
             have i₂ := b1e80 x
             grind)
          | exact superpose b1e80 b1e25
          | exact resolve b1e25 b1e80
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e80
        have b1e139 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e129
             have i₂ := b1e27
             grind)
          | exact superpose b1e27 b1e129
          | exact resolve b1e129 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27 b1e129
        have b1e140 : False := by grind
        exact b1e140
      · have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e22 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e25 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b2e61 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X1 X0
             have i₂ := b2e17 X1 X0
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X1 X0
             have j1 := b2e17 (M.op X0 X1) (k X1 X0)
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 (M.op (M.op X0 X1) (M.op X0 X0)) (M.op X1 X0)
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 (M.op X1 X0) (M.op (M.op X0 X1) (M.op X0 X0))
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e63 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e61 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61
        have b2e64 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e63 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e63
        have b2e68 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e25 X0 X1
             have i₂ := b2e64 (τ X0) X1
             grind)
          | exact superpose b2e64 b2e25
          | (have j1 := b2e64 (k (σ X1) X0) (σ (M.op (τ X0) X1))
             grind)
          | exact resolve b2e25 b2e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25
        have b2e69 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e64 (σ X0) (σ X1)
             grind)
          | exact superpose b2e64 b2e18
          | (have j1 := b2e64 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
             grind)
          | exact resolve b2e18 b2e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e64
        have b2e153 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e68 (σ X0) X1
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e68
          | exact resolve b2e68 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e68
        have b2e169 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e153 X0 X1
             have i₂ := b2e18 X1 X0
             grind)
          | exact superpose b2e18 b2e153
          | (have j0 := b2e153 (σ (k X1 X0)) (σ (M.op X0 X1))
             grind)
          | exact resolve b2e153 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e153
        have b2e482 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e69 x y
             grind)
          | exact superpose b2e69 b2e19
          | (have j1 := b2e69 x y
             grind)
          | exact resolve b2e19 b2e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e69
        have b2e496 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have r₁ := b2e482
             have r₂ := b2e22
             grind)
          | exact resolve b2e482 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e482
        have b2e506 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
          first
          | (have i₁ := b2e496
             have i₂ := b2e169 x y
             grind)
          | exact superpose b2e169 b2e496
          | (have j1 := b2e169 x y
             grind)
          | (have r₁ := b2e496
             have r₂ := b2e169 x y
             grind)
          | (have r₁ := b2e496
             have r₂ := b2e169 (σ (M.op x y)) (σ (k y x))
             grind)
          | (have r₁ := b2e496
             have r₂ := b2e169 (σ (k y x)) (σ (M.op x y))
             grind)
          | exact resolve b2e496 b2e169
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e169 b2e496
        have b2e507 : x = y := by grind
        clear b2e506
        have b2e561 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e507
             grind)
          | exact superpose b2e507 b2e22
          | exact resolve b2e22 b2e507
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e507
        have b2e565 : False := by grind
        exact b2e565
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) (M.op (σ y) (σ x)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = (M.op X1 X0) ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e21 : x = y := by grind
        have b3e22 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e51 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by grind
        have b3e52 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by grind
        clear b3e51
        have b3e53 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e52
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e52
          | exact resolve b3e52 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52
        have b3e58 : (σ (M.op y y)) ≠ (σ (k y y)) := by grind
        clear b3e53
        have b3e65 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          grind
        have b3e68 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e65 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e65
        have b3e69 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e68 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e68
        have b3e93 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e58
             have i₂ := b3e69 y
             grind)
          | exact superpose b3e69 b3e58
          | exact resolve b3e58 b3e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e58 b3e69
        have b3e94 : False := by grind
        exact b3e94
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = (M.op X1 X0) ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = y := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e67 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            grind
          have b4e70 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e67 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e67
          have b4e71 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e70 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e70
          have b4e75 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e71 (σ X0)
               grind)
            | exact superpose b4e71 b4e19
            | exact resolve b4e19 b4e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e84 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e75 X0
               have i₂ := b4e71 X0
               grind)
            | exact superpose b4e71 b4e75
            | exact resolve b4e75 b4e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e71 b4e75
          have b4e111 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
          clear b4e84
          have b4e117 : False := by grind
          exact b4e117
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) (M.op (σ y) (σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e21 : x ≠ y := by grind
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
        have b6e65 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e15 X1 X0
             have i₂ := b6e17 X1 X0
             grind)
          | exact superpose b6e17 b6e15
          | (have j0 := b6e15 X1 X0
             have j1 := b6e17 (M.op X0 X1) (k X1 X0)
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 (M.op (M.op X0 X1) (M.op X0 X0)) (M.op X1 X0)
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 (M.op X1 X0) (M.op (M.op X0 X1) (M.op X0 X0))
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e67 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e65 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e65
        have b6e68 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e67 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e67
        have b6e72 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X1 X0
             have i₂ := b6e68 (σ X0) (σ X1)
             grind)
          | exact superpose b6e68 b6e18
          | (have j1 := b6e68 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
             grind)
          | exact resolve b6e18 b6e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e73 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e24 X1 X0
             have i₂ := b6e68 X0 (τ X1)
             grind)
          | exact superpose b6e68 b6e24
          | (have j1 := b6e68 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
             grind)
          | exact resolve b6e24 b6e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24 b6e68
        have b6e171 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e73 X0 (σ X0)
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e73
          | exact resolve b6e73 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e73
        have b6e187 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e171 X0 X1
             have i₂ := b6e18 X0 X1
             grind)
          | exact superpose b6e18 b6e171
          | (have j0 := b6e171 (σ (k X0 X1)) (σ (M.op X1 X0))
             grind)
          | exact resolve b6e171 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e171
        have b6e505 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e72 x y
             grind)
          | exact superpose b6e72 b6e19
          | (have j1 := b6e72 x y
             grind)
          | exact resolve b6e19 b6e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e72
        have b6e543 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
          first
          | (have i₁ := b6e505
             have i₂ := b6e187 y x
             grind)
          | exact superpose b6e187 b6e505
          | (have j1 := b6e187 (σ x) (σ y)
             grind)
          | (have r₁ := b6e505
             have r₂ := b6e187 y x
             grind)
          | (have r₁ := b6e505
             have r₂ := b6e187 (σ (M.op x y)) (σ (k y x))
             grind)
          | (have r₁ := b6e505
             have r₂ := b6e187 (σ (k y x)) (σ (M.op x y))
             grind)
          | exact resolve b6e505 b6e187
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e187 b6e505
        have b6e544 : (σ x) = (σ y) ∨ x = y := by grind
        clear b6e543
        have b6e546 : (σ x) = (σ y) := by
          first
          | (have r₁ := b6e544
             have r₂ := b6e21
             grind)
          | exact resolve b6e544 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e544
        have b6e569 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e546
             grind)
          | exact superpose b6e546 b6e13
          | exact resolve b6e13 b6e546
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e546
        have b6e600 : x = y := by
          first
          | (have i₁ := b6e569
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e569
          | exact resolve b6e569 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e569
        have b6e606 : False := by grind
        exact b6e606
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e22 : x ≠ y := by grind
          have b7e24 : (σ x) = (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e28 : y = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 y
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e14
            | exact resolve b7e14 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e29 : x = y := by
            first
            | (have i₁ := b7e28
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e28
            | exact resolve b7e28 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28
          have b7e30 : False := by grind
          exact b7e30
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : x ≠ y := by grind
          have b8e24 : (σ x) ≠ (σ y) := by grind
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
          have b8e88 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X1 X0
               have i₂ := b8e18 X1 X0
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X1 X0
               have j1 := b8e18 (M.op X0 X1) (k X1 X0)
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 (M.op (M.op X0 X1) (M.op X0 X0)) (M.op X1 X0)
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 (M.op X1 X0) (M.op (M.op X0 X1) (M.op X0 X0))
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e90 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e88 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e88
          have b8e91 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e90 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e90
          have b8e95 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e91 (σ X0) (σ X1)
               grind)
            | exact superpose b8e91 b8e19
            | (have j1 := b8e91 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
               grind)
            | exact resolve b8e19 b8e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e97 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X1 X0
               have i₂ := b8e91 X0 (τ X1)
               grind)
            | exact superpose b8e91 b8e26
            | (have j1 := b8e91 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
               grind)
            | exact resolve b8e26 b8e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e91
          have b8e134 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
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
          clear b8e97
          have b8e150 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e134 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e134
            | (have j0 := b8e134 (σ (k X0 X1)) (σ (M.op X1 X0))
               grind)
            | exact resolve b8e134 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e134
          have b8e479 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
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
          clear b8e95
          have b8e493 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have r₁ := b8e479
               have r₂ := b8e24
               grind)
            | exact resolve b8e479 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e479
          have b8e503 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
            first
            | (have i₁ := b8e493
               have i₂ := b8e150 y x
               grind)
            | exact superpose b8e150 b8e493
            | (have j1 := b8e150 x y
               grind)
            | (have r₁ := b8e493
               have r₂ := b8e150 y x
               grind)
            | (have r₁ := b8e493
               have r₂ := b8e150 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e493
               have r₂ := b8e150 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e493 b8e150
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e150 b8e493
          have b8e504 : x = y := by grind
          clear b8e503
          have b8e506 : False := by grind
          exact b8e506

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(X,Y),m(X,X)) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppxypxx_y_x_y_pxy_pxx_pxy_Equation1 :
    AutBox.GuardAut2 (((Lf 0) ⋆ (Lf 1)) ⋆ ((Lf 0) ⋆ (Lf 0))) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 0) ⋆ (Lf 1)) ⋆ ((Lf 0) ⋆ (Lf 0))) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op a b) (M.op a a) ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op a b) (M.op a a)) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op a b) (M.op a a) = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op (M.op a b) (M.op a a)) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op a b) (M.op a a) = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op a b) (M.op a a)) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op x y) (M.op x x)) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ((σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op (M.op x y) (M.op x x)) := by grind
      have b0e20 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e30 : y ≠ y ∨ (M.op x y) = (k x y) := by
        first
        | (have i₁ := b0e14 x y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 x y
           grind)
        | (have r₁ := b0e14 x y
           have r₂ := b0e19
           grind)
        | exact resolve b0e14 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e31 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have i₁ := b0e14 (σ x) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have j0 := b0e14 (σ x) (σ y)
           grind)
        | (have r₁ := b0e14 (σ x) (σ y)
           have r₂ := b0e20
           grind)
        | exact resolve b0e14 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e32 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
      clear b0e31
      have b0e33 : (M.op x y) = (k x y) := by grind
      clear b0e30
      have b0e34 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e32
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e32
        | exact resolve b0e32 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32
      have b0e35 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e34
           have i₂ := b0e33
           grind)
        | exact superpose b0e33 b0e34
        | exact resolve b0e34 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33 b0e34
      have b0e36 : False := by grind
      exact b0e36
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e25 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e19
          | exact resolve b1e19 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e26 : y = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 y
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e13
          | exact resolve b1e13 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e27 : x = y := by
          first
          | (have i₁ := b1e26
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e26
          | exact resolve b1e26 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e61 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          grind
        have b1e65 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e61 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61
        have b1e66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e65 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e65
        have b1e70 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e66 (σ X0)
             grind)
          | exact superpose b1e66 b1e18
          | exact resolve b1e18 b1e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e70 X0
             have i₂ := b1e66 X0
             grind)
          | exact superpose b1e66 b1e70
          | exact resolve b1e70 b1e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e66 b1e70
        have b1e146 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e25
             have i₂ := b1e73 x
             grind)
          | exact superpose b1e73 b1e25
          | exact resolve b1e25 b1e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e73
        have b1e157 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e146
             have i₂ := b1e27
             grind)
          | exact superpose b1e27 b1e146
          | exact resolve b1e146 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27 b1e146
        have b1e158 : False := by grind
        exact b1e158
      · have b2e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X1 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : y = (M.op (M.op x y) (M.op x x)) := by grind
        have b2e22 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e39 : y ≠ y ∨ (M.op x y) = (k x y) := by
          first
          | (have i₁ := b2e15 x y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e15
          | (have j0 := b2e15 x y
             grind)
          | (have r₁ := b2e15 x y
             have r₂ := b2e20
             grind)
          | exact resolve b2e15 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e40 : (M.op x y) = (k x y) := by grind
        clear b2e39
        have b2e61 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X1 X0
             have i₂ := b2e17 X1 X0
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X1 X0
             have j1 := b2e17 (k X1 X0) (M.op X1 X0)
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 (M.op (M.op X0 X1) (M.op X0 X0)) X1
             grind)
          | (have r₁ := b2e15 X0 X0
             have r₂ := b2e17 X0 (M.op (M.op X0 X0) (M.op X0 X0))
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e63 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e61 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61
        have b2e64 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e63 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e63
        have b2e70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e64 (σ X1) (σ X0)
             grind)
          | exact superpose b2e64 b2e18
          | (have j1 := b2e64 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
             grind)
          | exact resolve b2e18 b2e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e64
        have b2e502 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e70 x y
             grind)
          | exact superpose b2e70 b2e19
          | (have j1 := b2e70 x y
             grind)
          | exact resolve b2e19 b2e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e70
        have b2e514 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e502
             have r₂ := b2e22
             grind)
          | exact resolve b2e502 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e502
        have b2e521 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b2e514
             have i₂ := b2e40
             grind)
          | exact superpose b2e40 b2e514
          | exact resolve b2e514 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40 b2e514
        have b2e522 : False := by grind
        exact b2e522
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ((σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e21 : x = y := by grind
        have b3e22 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e35 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by grind
        have b3e36 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by grind
        clear b3e35
        have b3e38 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e36
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e36
          | exact resolve b3e36 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e36
        have b3e48 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          grind
        have b3e52 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e48 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48
        have b3e53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e52 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52
        have b3e75 : (σ (M.op y y)) ≠ (σ (k y y)) := by grind
        clear b3e38
        have b3e81 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e75
             have i₂ := b3e53 y
             grind)
          | exact superpose b3e53 b3e75
          | exact resolve b3e75 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53 b3e75
        have b3e82 : False := by grind
        exact b3e82
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = y := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e46 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            grind
          have b4e50 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e46 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46
          have b4e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e50 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e50
          have b4e55 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e51 (σ X0)
               grind)
            | exact superpose b4e51 b4e19
            | exact resolve b4e19 b4e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e60 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e55 X0
               have i₂ := b4e51 X0
               grind)
            | exact superpose b4e51 b4e55
            | exact resolve b4e55 b4e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e51 b4e55
          have b4e118 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
          clear b4e60
          have b4e125 : False := by grind
          exact b4e125
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ((σ y)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X1 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e21 : x ≠ y := by grind
        have b6e22 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e39 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e15
          | (have j0 := b6e15 (σ x) (σ y)
             grind)
          | (have r₁ := b6e15 (σ x) (σ y)
             have r₂ := b6e22
             grind)
          | exact resolve b6e15 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e40 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b6e39
        have b6e41 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e40
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e40
          | exact resolve b6e40 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40
        have b6e43 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e41
             grind)
          | exact superpose b6e41 b6e19
          | exact resolve b6e19 b6e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41
        have b6e66 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e15 X1 X0
             have i₂ := b6e17 X1 X0
             grind)
          | exact superpose b6e17 b6e15
          | (have j0 := b6e15 X1 X0
             have j1 := b6e17 (k X1 X0) (M.op X1 X0)
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 (M.op (M.op X0 X1) (M.op X0 X0)) X1
             grind)
          | (have r₁ := b6e15 X0 X0
             have r₂ := b6e17 X0 (M.op (M.op X0 X0) (M.op X0 X0))
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e68 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e66 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e66
        have b6e69 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e68 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e68
        have b6e82 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
          first
          | (have i₁ := b6e43
             have i₂ := b6e69 y x
             grind)
          | exact superpose b6e69 b6e43
          | (have j1 := b6e69 x y
             grind)
          | (have r₁ := b6e43
             have r₂ := b6e69 (σ (M.op x y)) (σ (k x y))
             grind)
          | (have r₁ := b6e43
             have r₂ := b6e69 (σ (k x y)) (σ (M.op x y))
             grind)
          | exact resolve b6e43 b6e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43 b6e69
        have b6e83 : x = y := by grind
        clear b6e82
        have b6e84 : False := by grind
        exact b6e84
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e22 : x ≠ y := by grind
          have b7e24 : (σ x) = (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e28 : y = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 y
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e14
            | exact resolve b7e14 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e29 : x = y := by
            first
            | (have i₁ := b7e28
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e28
            | exact resolve b7e28 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28
          have b7e30 : False := by grind
          exact b7e30
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X1 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : x ≠ y := by grind
          have b8e24 : (σ x) ≠ (σ y) := by grind
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
          have b8e60 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X1 X0
               have i₂ := b8e18 X1 X0
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X1 X0
               have j1 := b8e18 (k X1 X0) (M.op X1 X0)
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 (M.op (M.op X0 X1) (M.op X0 X0)) X1
               grind)
            | (have r₁ := b8e16 X0 X0
               have r₂ := b8e18 X0 (M.op (M.op X0 X0) (M.op X0 X0))
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e62 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e60 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60
          have b8e63 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e62 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62
          have b8e68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e63 (σ X1) (σ X0)
               grind)
            | exact superpose b8e63 b8e19
            | (have j1 := b8e63 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
               grind)
            | exact resolve b8e19 b8e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e69 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X0 X1
               have i₂ := b8e63 X1 (τ X0)
               grind)
            | exact superpose b8e63 b8e26
            | (have j1 := b8e63 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
               grind)
            | exact resolve b8e26 b8e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e63
          have b8e158 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e69 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e69
            | exact resolve b8e69 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e69
          have b8e174 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e158 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e158
            | (have j0 := b8e158 (σ (k X0 X1)) (σ (M.op X0 X1))
               grind)
            | exact resolve b8e158 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e158
          have b8e492 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e68 x y
               grind)
            | exact superpose b8e68 b8e20
            | (have j1 := b8e68 x y
               grind)
            | exact resolve b8e20 b8e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e68
          have b8e504 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e492
               have r₂ := b8e24
               grind)
            | exact resolve b8e492 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e492
          have b8e515 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
            first
            | (have i₁ := b8e504
               have i₂ := b8e174 x y
               grind)
            | exact superpose b8e174 b8e504
            | (have j1 := b8e174 x y
               grind)
            | (have r₁ := b8e504
               have r₂ := b8e174 x y
               grind)
            | (have r₁ := b8e504
               have r₂ := b8e174 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e504
               have r₂ := b8e174 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e504 b8e174
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e174 b8e504
          have b8e516 : x = y := by grind
          clear b8e515
          have b8e518 : False := by grind
          exact b8e518
