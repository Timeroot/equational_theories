import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(Y,X),X) = m(Y,X) then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppyxx_pyx_pxy_x_pxy_x_pxy_Equation1 :
    AutBox.GuardAut2 (((Lf 1) ⋆ (Lf 0)) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 1) ⋆ (Lf 0)) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op b a) a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op b a) a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op b a) a = M.op b a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op (M.op b a) a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op b a) a = M.op b a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op b a) a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op y x) x) (M.op y x) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ y) (σ x)) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op X1 X0) X0) ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op y x) = (M.op (M.op y x) x) := by grind
      have b0e20 : (M.op (σ y) (σ x)) = (M.op (M.op (σ y) (σ x)) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e29 : (M.op y x) ≠ (M.op y x) ∨ (M.op x y) = (k x y) := by
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
      have b0e30 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
      have b0e31 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
      clear b0e30
      have b0e32 : (M.op x y) = (k x y) := by grind
      clear b0e29
      have b0e33 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e31
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e31
        | exact resolve b0e31 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31
      have b0e36 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e33
           have i₂ := b0e32
           grind)
        | exact superpose b0e32 b0e33
        | exact resolve b0e33 b0e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32 b0e33
      have b0e37 : False := by grind
      exact b0e37
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op X1 X0) X0) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (M.op (M.op X1 X0) X0) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op y x) = (M.op (M.op y x) x) := by grind
        have b1e21 : (M.op (σ y) (σ x)) ≠ (M.op (M.op (σ y) (σ x)) (σ x)) := by grind
        have b1e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e19
          | exact resolve b1e19 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e40 : (M.op y x) ≠ (M.op y x) ∨ (M.op x y) = (k x y) := by
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
        have b1e41 : (M.op x y) = (k x y) := by grind
        clear b1e40
        have b1e45 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (M.op (M.op (σ y) (σ x)) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e48 : (M.op (σ y) (σ x)) = (M.op (M.op (σ y) (σ x)) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e45
        have b1e49 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e48
             have r₂ := b1e21
             grind)
          | exact resolve b1e48 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e48
        have b1e50 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e49
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e49
          | exact resolve b1e49 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49
        have b1e51 : (σ (M.op x y)) = (σ x) := by
          first
          | (have i₁ := b1e50
             have i₂ := b1e41
             grind)
          | exact superpose b1e41 b1e50
          | exact resolve b1e50 b1e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41 b1e50
        have b1e52 : False := by grind
        exact b1e52
      · have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op X1 X0) X0) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op y x) = (M.op (M.op y x) x) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e38 : (M.op y x) ≠ (M.op y x) ∨ (M.op x y) = (k x y) := by
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
        have b2e39 : (M.op x y) = (k x y) := by grind
        clear b2e38
        have b2e54 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
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
          | (have r₁ := b2e15 X1 X1
             have r₂ := b2e17 (M.op X1 X1) X1
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e58 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e54 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e54
        have b2e59 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e58 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e58
        have b2e87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e59 (σ X1) (σ X0)
             grind)
          | exact superpose b2e59 b2e18
          | (have j1 := b2e59 (σ X1) (σ X0)
             grind)
          | exact resolve b2e18 b2e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e59
        have b2e336 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e87 x y
             grind)
          | exact superpose b2e87 b2e19
          | (have j1 := b2e87 x y
             grind)
          | exact resolve b2e19 b2e87
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e87
        have b2e346 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e336
             have r₂ := b2e22
             grind)
          | exact resolve b2e336 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e336
        have b2e350 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b2e346
             have i₂ := b2e39
             grind)
          | exact superpose b2e39 b2e346
          | exact resolve b2e346 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39 b2e346
        have b2e351 : False := by grind
        exact b2e351
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ y) (σ x)) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op X1 X0) X0) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (M.op (M.op X1 X0) X0) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : (M.op y x) ≠ (M.op (M.op y x) x) := by grind
        have b3e21 : x = (M.op x y) := by grind
        have b3e22 : (M.op (σ y) (σ x)) = (M.op (M.op (σ y) (σ x)) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e19
          | exact resolve b3e19 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e40 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b3e41 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b3e40
        have b3e42 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e41
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e41
          | exact resolve b3e41 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e41
        have b3e45 : x ≠ x ∨ (M.op y x) = (M.op (M.op y x) x) ∨ x = (k x y) := by
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
        have b3e48 : (M.op y x) = (M.op (M.op y x) x) ∨ x = (k x y) := by grind
        clear b3e45
        have b3e49 : x = (k x y) := by
          first
          | (have r₁ := b3e48
             have r₂ := b3e20
             grind)
          | exact resolve b3e48 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48
        have b3e61 : (σ x) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e42
             grind)
          | exact superpose b3e42 b3e23
          | exact resolve b3e23 b3e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e42
        have b3e66 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b3e61
             have i₂ := b3e49
             grind)
          | exact superpose b3e49 b3e61
          | exact resolve b3e61 b3e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49 b3e61
        have b3e67 : False := by grind
        exact b3e67
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op x y) := by grind
          have b4e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e25 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e26 : (σ x) ≠ (σ x) := by
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
        · have b5e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op X1 X0) X0) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (M.op (M.op X1 X0) X0) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op y x) ≠ (M.op (M.op y x) x) := by grind
          have b5e22 : x = (M.op x y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e42 : x ≠ x ∨ (M.op y x) = (M.op (M.op y x) x) ∨ x = (k x y) := by
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
          have b5e43 : (M.op y x) = (M.op (M.op y x) x) ∨ x = (k x y) := by grind
          clear b5e42
          have b5e44 : x = (k x y) := by
            first
            | (have r₁ := b5e43
               have r₂ := b5e21
               grind)
            | exact resolve b5e43 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43
          have b5e49 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
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
            | (have r₁ := b5e16 X1 X1
               have r₂ := b5e18 (M.op X1 X1) X1
               grind)
            | exact resolve b5e16 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e53 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e49 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49
          have b5e54 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e53 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53
          have b5e69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X0 X1
               have i₂ := b5e54 (σ X1) (σ X0)
               grind)
            | exact superpose b5e54 b5e19
            | (have j1 := b5e54 (σ X1) (σ X0)
               grind)
            | exact resolve b5e19 b5e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e54
          have b5e336 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e69 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e69
          have b5e476 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e336 x y
               have i₂ := b5e44
               grind)
            | exact superpose b5e44 b5e336
            | (have j0 := b5e336 x y
               grind)
            | exact resolve b5e336 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44 b5e336
          have b5e481 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b5e476
          have b5e484 : False := by grind
          exact b5e484
    · rcases eq_or_ne (M.op (M.op (σ y) (σ x)) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op X1 X0) X0) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e21 : x ≠ (M.op x y) := by grind
        have b6e22 : (M.op (σ y) (σ x)) = (M.op (M.op (σ y) (σ x)) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e38 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b6e39 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b6e38
        have b6e40 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e39
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e39
          | exact resolve b6e39 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39
        have b6e42 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e40
             grind)
          | exact superpose b6e40 b6e19
          | exact resolve b6e19 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40
        have b6e52 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
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
          | (have r₁ := b6e15 X1 X1
             have r₂ := b6e17 (M.op X1 X1) X1
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e56 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e52 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e52
        have b6e57 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e56 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e56
        have b6e72 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e42
             have i₂ := b6e57 y x
             grind)
          | exact superpose b6e57 b6e42
          | (have j1 := b6e57 y x
             grind)
          | exact resolve b6e42 b6e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42 b6e57
        have b6e73 : x = (M.op x y) := by grind
        clear b6e72
        have b6e74 : False := by grind
        exact b6e74
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op X1 X0) X0) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (M.op (M.op X1 X0) X0) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op x y) := by grind
          have b7e23 : (M.op (σ y) (σ x)) ≠ (M.op (M.op (σ y) (σ x)) (σ x)) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e43 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (M.op (M.op (σ y) (σ x)) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e44 : (M.op (σ y) (σ x)) = (M.op (M.op (σ y) (σ x)) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e43
          have b7e45 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e44
               have r₂ := b7e23
               grind)
            | exact resolve b7e44 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e46 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e45
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e45
            | exact resolve b7e45 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e49 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e46
               grind)
            | exact superpose b7e46 b7e14
            | exact resolve b7e14 b7e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e50 : x = (k x y) := by
            first
            | (have i₁ := b7e49
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e49
            | exact resolve b7e49 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e57 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
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
            | (have r₁ := b7e16 X1 X1
               have r₂ := b7e18 (M.op X1 X1) X1
               grind)
            | exact resolve b7e16 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e61 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e57 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e62 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e61 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e87 : x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e50
               have i₂ := b7e62 y x
               grind)
            | exact superpose b7e62 b7e50
            | (have j1 := b7e62 y x
               grind)
            | exact resolve b7e50 b7e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50 b7e62
          have b7e89 : x = (M.op x y) := by grind
          clear b7e87
          have b7e92 : False := by grind
          exact b7e92
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op X1 X0) X0) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : x ≠ (M.op x y) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
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
          have b8e50 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
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
            | (have r₁ := b8e16 X1 X1
               have r₂ := b8e18 (M.op X1 X1) X1
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e54 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e50 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e50
          have b8e55 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e54 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e54
          have b8e71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e55 (σ X1) (σ X0)
               grind)
            | exact superpose b8e55 b8e19
            | (have j1 := b8e55 (σ X1) (σ X0)
               grind)
            | exact resolve b8e19 b8e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e74 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X1 X0
               have i₂ := b8e55 (τ X1) X0
               grind)
            | exact superpose b8e55 b8e26
            | (have j1 := b8e55 (τ X1) X0
               grind)
            | exact resolve b8e26 b8e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e55
          have b8e208 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e74 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e74
            | exact resolve b8e74 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e74
          have b8e233 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e208 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e208
            | (have j0 := b8e208 X0 X1
               grind)
            | exact resolve b8e208 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e208
          have b8e355 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e71 x y
               grind)
            | exact superpose b8e71 b8e20
            | (have j1 := b8e71 x y
               grind)
            | exact resolve b8e20 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e71
          have b8e365 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e355
               have r₂ := b8e24
               grind)
            | exact resolve b8e355 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e355
          have b8e370 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e365
               have i₂ := b8e233 y x
               grind)
            | exact superpose b8e233 b8e365
            | (have j1 := b8e233 y x
               grind)
            | (have r₁ := b8e365
               have r₂ := b8e233 y x
               grind)
            | exact resolve b8e365 b8e233
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e233 b8e365
          have b8e371 : x = (M.op x y) := by grind
          clear b8e370
          have b8e373 : False := by grind
          exact b8e373

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(Y,X),Y) = m(m(Y,Y),Y) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppyxy_ppyyy_x_y_pxy_x_pxy_Equation1 :
    AutBox.GuardAut2 (((Lf 1) ⋆ (Lf 0)) ⋆ (Lf 1)) (((Lf 1) ⋆ (Lf 1)) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 1) ⋆ (Lf 0)) ⋆ (Lf 1)) (((Lf 1) ⋆ (Lf 1)) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op b a) b ≠ M.op (M.op b b) b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op b a) b) (M.op (M.op b b) b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op b a) b = M.op (M.op b b) b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op (M.op b a) b) (M.op (M.op b b) b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op b a) b = M.op (M.op b b) b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op b a) b) (M.op (M.op b b) b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op y x) y) (M.op (M.op y y) y) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ y) (σ x)) (σ y)) (M.op (M.op (σ y) (σ y)) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) ≠ (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op (M.op y x) y) = (M.op (M.op y y) y) := by grind
      have b0e20 : (M.op (M.op (σ y) (σ x)) (σ y)) = (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e44 : (M.op (M.op y y) y) ≠ (M.op (M.op y y) y) ∨ (M.op x y) = (k x y) := by
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
      have b0e45 : (M.op (M.op (σ y) (σ y)) (σ y)) ≠ (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
      have b0e47 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
      clear b0e45
      have b0e48 : (M.op x y) = (k x y) := by grind
      clear b0e44
      have b0e49 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e47
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e47
        | exact resolve b0e47 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47
      have b0e50 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e49
           have i₂ := b0e48
           grind)
        | exact superpose b0e48 b0e49
        | exact resolve b0e49 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48 b0e49
      have b0e51 : False := by grind
      exact b0e51
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e21 : (M.op (M.op (σ y) (σ x)) (σ y)) ≠ (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
        have b1e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (M.op (M.op (σ y) (σ y)) (σ y)) ≠ (M.op (M.op (σ y) (σ y)) (σ y)) := by
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
      · have b2e15 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) ≠ (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = (M.op (M.op X1 X1) X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op (M.op y x) y) = (M.op (M.op y y) y) := by grind
        have b2e22 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e38 : (M.op (M.op y y) y) ≠ (M.op (M.op y y) y) ∨ (M.op x y) = (k x y) := by
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
        have b2e40 : (M.op x y) = (k x y) := by grind
        clear b2e38
        have b2e53 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X1 X0
             have i₂ := b2e17 X1 X0
             grind)
          | (have i₁ := b2e15 X1 X1
             have i₂ := b2e17 X0 X1
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X0 X0
             have j1 := b2e17 (M.op X1 X0) (k X1 X0)
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X0 X0
             have r₂ := b2e17 X0 X0
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 (M.op (M.op X1 X0) X1) (M.op (M.op X1 X1) X1)
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e57 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e53 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53
        have b2e58 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e57 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57
        have b2e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e58 (σ X1) (σ X0)
             grind)
          | exact superpose b2e58 b2e18
          | (have j1 := b2e58 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
             grind)
          | exact resolve b2e18 b2e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e58
        have b2e476 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e62 x y
             grind)
          | exact superpose b2e62 b2e19
          | (have j1 := b2e62 x y
             grind)
          | exact resolve b2e19 b2e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e62
        have b2e491 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e476
             have r₂ := b2e22
             grind)
          | exact resolve b2e476 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e476
        have b2e497 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b2e491
             have i₂ := b2e40
             grind)
          | exact superpose b2e40 b2e491
          | exact resolve b2e491 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40 b2e491
        have b2e498 : False := by grind
        exact b2e498
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ y) (σ x)) (σ y)) (M.op (M.op (σ y) (σ y)) (σ y)) with h1a | h1a
      · have b3e20 : (M.op (M.op y x) y) ≠ (M.op (M.op y y) y) := by grind
        have b3e21 : x = y := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e27 : False := by grind
        exact b3e27
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e22 : x = y := by grind
          have b4e23 : (M.op (M.op (σ y) (σ x)) (σ y)) ≠ (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e30 : False := by grind
          exact b4e30
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (M.op (σ y) (σ x)) (σ y)) (M.op (M.op (σ y) (σ y)) (σ y)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) ≠ (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = (M.op (M.op X1 X1) X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e21 : x ≠ y := by grind
        have b6e22 : (M.op (M.op (σ y) (σ x)) (σ y)) = (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e38 : (M.op (M.op (σ y) (σ y)) (σ y)) ≠ (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b6e40 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b6e38
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
        have b6e54 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e15 X1 X0
             have i₂ := b6e17 X1 X0
             grind)
          | (have i₁ := b6e15 X1 X1
             have i₂ := b6e17 X0 X1
             grind)
          | exact superpose b6e17 b6e15
          | (have j0 := b6e15 X0 X0
             have j1 := b6e17 (M.op X1 X0) (k X1 X0)
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X0 X0
             have r₂ := b6e17 X0 X0
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 (M.op (M.op X1 X0) X1) (M.op (M.op X1 X1) X1)
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e58 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e54 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e54
        have b6e59 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e58 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58
        have b6e61 : (σ (M.op x y)) ≠ (σ (k x y)) := by
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
        have b6e66 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
          first
          | (have i₁ := b6e61
             have i₂ := b6e59 y x
             grind)
          | exact superpose b6e59 b6e61
          | (have j1 := b6e59 x y
             grind)
          | (have r₁ := b6e61
             have r₂ := b6e59 (σ (M.op x y)) (σ (k x y))
             grind)
          | (have r₁ := b6e61
             have r₂ := b6e59 (σ (k x y)) (σ (M.op x y))
             grind)
          | exact resolve b6e61 b6e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e59 b6e61
        have b6e67 : x = y := by grind
        clear b6e66
        have b6e68 : False := by grind
        exact b6e68
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b7e23 : (M.op (M.op (σ y) (σ x)) (σ y)) ≠ (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
          have b7e24 : (σ x) = (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : (M.op (M.op (σ y) (σ y)) (σ y)) ≠ (M.op (M.op (σ y) (σ y)) (σ y)) := by
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
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) ≠ (M.op (M.op X1 X1) X1) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = (M.op (M.op X1 X1) X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
          have b8e66 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
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
               have j1 := b8e18 (M.op X1 X0) (k X1 X0)
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 (M.op (M.op X1 X0) X1) (M.op (M.op X1 X1) X1)
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e70 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e66 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66
          have b8e71 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e70 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e70
          have b8e75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e71 (σ X1) (σ X0)
               grind)
            | exact superpose b8e71 b8e19
            | (have j1 := b8e71 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
               grind)
            | exact resolve b8e19 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e76 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X0 X1
               have i₂ := b8e71 X1 (τ X0)
               grind)
            | exact superpose b8e71 b8e26
            | (have j1 := b8e71 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
               grind)
            | exact resolve b8e26 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e71
          have b8e130 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e76 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e76
            | exact resolve b8e76 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e76
          have b8e146 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e130 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e130
            | (have j0 := b8e130 (σ (k X0 X1)) (σ (M.op X0 X1))
               grind)
            | exact resolve b8e130 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e130
          have b8e474 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e75 x y
               grind)
            | exact superpose b8e75 b8e20
            | (have j1 := b8e75 x y
               grind)
            | exact resolve b8e20 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e75
          have b8e489 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e474
               have r₂ := b8e24
               grind)
            | exact resolve b8e474 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e474
          have b8e498 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
            first
            | (have i₁ := b8e489
               have i₂ := b8e146 x y
               grind)
            | exact superpose b8e146 b8e489
            | (have j1 := b8e146 x y
               grind)
            | (have r₁ := b8e489
               have r₂ := b8e146 x y
               grind)
            | (have r₁ := b8e489
               have r₂ := b8e146 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e489
               have r₂ := b8e146 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e489 b8e146
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e146 b8e489
          have b8e499 : x = y := by grind
          clear b8e498
          have b8e501 : False := by grind
          exact b8e501

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(Y,X),Y) = m(Y,X) then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppyxy_pyx_pyx_y_pyx_y_pyx_Equation1 :
    AutBox.GuardAut2 (((Lf 1) ⋆ (Lf 0)) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 1) ⋆ (Lf 0)) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op b a) b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op (M.op b a) b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op b a) b = M.op b a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op (M.op b a) b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op b a) b = M.op b a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op (M.op b a) b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op y x) y) (M.op y x) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ y) (σ x)) (σ y)) (M.op (σ y) (σ x)) with h1a | h1a
    · have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op X1 X0) X1) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (M.op (M.op X1 X0) X1) ∨ (k X0 X1) = X1 := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e21 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 (τ X0) X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e17
        | exact resolve b0e17 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e43 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 X1 X0
           have i₂ := b0e16 X1 X0
           grind)
        | exact superpose b0e16 b0e14
        | (have j0 := b0e14 X1 X0
           have j1 := b0e16 X1 X0
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | (have r₁ := b0e14 X0 X0
           have r₂ := b0e16 X0 (M.op X0 X0)
           grind)
        | exact resolve b0e14 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e47 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e43 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43
      have b0e48 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e47 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47
      have b0e78 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X1 X0
           have i₂ := b0e48 (σ X0) (σ X1)
           grind)
        | exact superpose b0e48 b0e17
        | (have j1 := b0e48 (σ X0) (σ X1)
           grind)
        | exact resolve b0e17 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e79 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e21 X1 X0
           have i₂ := b0e48 X0 (τ X1)
           grind)
        | exact superpose b0e48 b0e21
        | (have j1 := b0e48 X0 (τ X1)
           grind)
        | exact resolve b0e21 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21 b0e48
      have b0e229 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e79 X0 (σ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e79
        | exact resolve b0e79 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e79
      have b0e254 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e229 X0 X1
           have i₂ := b0e17 X0 X1
           grind)
        | exact superpose b0e17 b0e229
        | (have j0 := b0e229 X0 X1
           grind)
        | exact resolve b0e229 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e229
      have b0e379 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e78 x y
           grind)
        | exact superpose b0e78 b0e18
        | (have j1 := b0e78 x y
           grind)
        | exact resolve b0e18 b0e78
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e387 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e78 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e78
      have b0e575 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e379
           have i₂ := b0e254 y x
           grind)
        | exact superpose b0e254 b0e379
        | (have j1 := b0e254 (σ y) (σ x)
           grind)
        | (have r₁ := b0e379
           have r₂ := b0e254 y x
           grind)
        | exact resolve b0e379 b0e254
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e379
      have b0e576 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
      clear b0e575
      have b0e579 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e576
           grind)
        | exact superpose b0e576 b0e18
        | exact resolve b0e18 b0e576
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e580 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e15 (σ y) (σ x)
           have i₂ := b0e576
           grind)
        | exact superpose b0e576 b0e15
        | (have j0 := b0e15 (σ y) (σ x)
           grind)
        | (have r₁ := b0e15 (σ y) (σ x)
           have r₂ := b0e576
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e576
           grind)
        | exact resolve b0e15 b0e576
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e581 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e14 (σ y) (σ x)
           have i₂ := b0e576
           grind)
        | exact superpose b0e576 b0e14
        | exact resolve b0e14 b0e576
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e576
      have b0e582 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
      clear b0e580
      have b0e583 : (σ x) = (σ (k y x)) ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e581
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e581
        | exact resolve b0e581 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e581
      have b0e584 : (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e582
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e582
        | exact resolve b0e582 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e582
      have b0e586 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
        first
        | (have r₁ := b0e584
           have r₂ := b0e583
           grind)
        | exact resolve b0e584 b0e583
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e583 b0e584
      have b0e719 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e254 y x
           have i₂ := b0e586
           grind)
        | exact superpose b0e586 b0e254
        | (have j0 := b0e254 y x
           grind)
        | exact resolve b0e254 b0e586
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e254 b0e586
      have b0e742 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
      clear b0e719
      have b0e763 : x = (M.op x y) := by
        first
        | (have r₁ := b0e742
           have r₂ := b0e579
           grind)
        | exact resolve b0e742 b0e579
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e579 b0e742
      have b0e843 : x ≠ x ∨ x = (M.op x x) ∨ x = (k y x) := by
        first
        | (have i₁ := b0e15 y x
           have i₂ := b0e763
           grind)
        | exact superpose b0e763 b0e15
        | (have j0 := b0e15 y x
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e763
           grind)
        | exact resolve b0e15 b0e763
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e844 : x ≠ (M.op x x) ∨ x = (k y x) := by
        first
        | (have i₁ := b0e14 y x
           have i₂ := b0e763
           grind)
        | exact superpose b0e763 b0e14
        | exact resolve b0e14 b0e763
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e845 : x = (M.op x x) ∨ x = (k y x) := by grind
      clear b0e843
      have b0e846 : x = (k y x) := by
        first
        | (have r₁ := b0e845
           have r₂ := b0e844
           grind)
        | exact resolve b0e845 b0e844
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e844 b0e845
      have b0e930 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e387 x y
           have i₂ := b0e846
           grind)
        | exact superpose b0e846 b0e387
        | (have j0 := b0e387 x y
           grind)
        | exact resolve b0e387 b0e846
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e387 b0e846
      have b0e934 : (σ x) = (M.op (σ x) (σ y)) := by grind
      clear b0e930
      have b0e1024 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e934
           grind)
        | exact superpose b0e934 b0e18
        | exact resolve b0e18 b0e934
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e934
      have b0e1030 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e1024
           have i₂ := b0e763
           grind)
        | exact superpose b0e763 b0e1024
        | exact resolve b0e1024 b0e763
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e763 b0e1024
      have b0e1031 : False := by grind
      exact b0e1031
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op X1 X0) X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (M.op (M.op X1 X0) X1) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : (M.op y x) = (M.op (M.op y x) y) := by grind
        have b1e21 : (M.op (σ y) (σ x)) ≠ (M.op (M.op (σ y) (σ x)) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e27 : (M.op y x) ≠ (M.op (M.op y x) (M.op y x)) ∨ (M.op y x) = (k y (M.op y x)) := by
          first
          | (have i₁ := b1e15 y (M.op y x)
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e15
          | (have r₁ := b1e15 x y
             have r₂ := b1e20
             grind)
          | exact resolve b1e15 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e28 : (M.op y x) ≠ (M.op y x) ∨ (M.op y x) = (k x y) := by
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
        have b1e29 : (M.op y x) = (k x y) := by grind
        clear b1e28
        have b1e30 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e31 : (M.op y x) ≠ (M.op y x) ∨ (M.op y x) = (M.op (M.op y x) (M.op y x)) ∨ (M.op y x) = (k y (M.op y x)) := by
          first
          | (have i₁ := b1e16 y (M.op y x)
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e16
          | (have j0 := b1e16 y (M.op y x)
             grind)
          | (have r₁ := b1e16 y (M.op y x)
             have r₂ := b1e20
             grind)
          | exact resolve b1e16 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e32 : (M.op y x) = (M.op (M.op y x) (M.op y x)) ∨ (M.op y x) = (k y (M.op y x)) := by grind
        clear b1e31
        have b1e33 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e30
        have b1e34 : (M.op y x) = (k y (M.op y x)) := by
          first
          | (have r₁ := b1e32
             have r₂ := b1e27
             grind)
          | exact resolve b1e32 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27 b1e32
        have b1e35 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e33
             have r₂ := b1e23
             grind)
          | exact resolve b1e33 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33
        have b1e36 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e35
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e35
          | exact resolve b1e35 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35
        have b1e37 : (σ y) = (σ (M.op y x)) := by
          first
          | (have i₁ := b1e36
             have i₂ := b1e29
             grind)
          | exact superpose b1e29 b1e36
          | exact resolve b1e36 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29 b1e36
        have b1e40 : (M.op y x) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (M.op y x)
             have i₂ := b1e37
             grind)
          | exact superpose b1e37 b1e13
          | exact resolve b1e13 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e41 : y = (M.op y x) := by
          first
          | (have i₁ := b1e40
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e40
          | exact resolve b1e40 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40
        have b1e44 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e15 X1 X0
             have i₂ := b1e17 X1 X0
             grind)
          | exact superpose b1e17 b1e15
          | (have j0 := b1e15 X1 X0
             have j1 := b1e17 X1 X0
             grind)
          | (have r₁ := b1e15 X0 X1
             have r₂ := b1e17 X0 X1
             grind)
          | (have r₁ := b1e15 X0 X0
             have r₂ := b1e17 X0 (M.op X0 X0)
             grind)
          | exact resolve b1e15 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e44 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e44
        have b1e49 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e48 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e48
        have b1e57 : y = (k y y) := by
          first
          | (have i₁ := b1e34
             have i₂ := b1e41
             grind)
          | exact superpose b1e41 b1e34
          | exact resolve b1e34 b1e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34 b1e41
        have b1e88 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X1 X0
             have i₂ := b1e49 (σ X0) (σ X1)
             grind)
          | exact superpose b1e49 b1e18
          | (have j1 := b1e49 (σ X0) (σ X1)
             grind)
          | exact resolve b1e18 b1e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49
        have b1e414 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e88 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e88
        have b1e521 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e414 y y
             have i₂ := b1e57
             grind)
          | exact superpose b1e57 b1e414
          | (have j0 := b1e414 y y
             grind)
          | exact resolve b1e414 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57 b1e414
        have b1e525 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b1e521
        have b1e529 : False := by grind
        exact b1e529
      · have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op X1 X0) X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (M.op (M.op X1 X0) X1) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op y x) = (M.op (M.op y x) y) := by grind
        have b2e21 : (M.op (σ y) (σ x)) ≠ (M.op (M.op (σ y) (σ x)) (σ y)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e37 : (M.op y x) ≠ (M.op (M.op y x) (M.op y x)) ∨ (M.op y x) = (k y (M.op y x)) := by
          first
          | (have i₁ := b2e15 y (M.op y x)
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e15
          | (have r₁ := b2e15 x y
             have r₂ := b2e20
             grind)
          | exact resolve b2e15 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e38 : (M.op y x) ≠ (M.op y x) ∨ (M.op y x) = (k x y) := by
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
        have b2e39 : (M.op y x) = (k x y) := by grind
        clear b2e38
        have b2e40 : (M.op y x) ≠ (M.op y x) ∨ (M.op y x) = (M.op (M.op y x) (M.op y x)) ∨ (M.op y x) = (k y (M.op y x)) := by
          first
          | (have i₁ := b2e16 y (M.op y x)
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e16
          | (have j0 := b2e16 y (M.op y x)
             grind)
          | (have r₁ := b2e16 y (M.op y x)
             have r₂ := b2e20
             grind)
          | exact resolve b2e16 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e41 : (M.op y x) = (M.op (M.op y x) (M.op y x)) ∨ (M.op y x) = (k y (M.op y x)) := by grind
        clear b2e40
        have b2e42 : (M.op y x) = (k y (M.op y x)) := by
          first
          | (have r₁ := b2e41
             have r₂ := b2e37
             grind)
          | exact resolve b2e41 b2e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37 b2e41
        have b2e44 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
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
          | (have r₁ := b2e15 X0 X0
             have r₂ := b2e17 X0 (M.op X0 X0)
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e44 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e44
        have b2e49 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e48 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48
        have b2e64 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e49 (σ X0) (σ X1)
             grind)
          | exact superpose b2e49 b2e18
          | (have j1 := b2e49 (σ X0) (σ X1)
             grind)
          | exact resolve b2e18 b2e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e49
        have b2e354 : (σ (k x y)) ≠ (M.op (σ (k x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e64 y x
             grind)
          | exact superpose b2e64 b2e21
          | (have j1 := b2e64 y x
             grind)
          | exact resolve b2e21 b2e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e361 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e64 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e64
        have b2e363 : (σ (k x y)) ≠ (M.op (σ (k x y)) (σ y)) := by
          first
          | (have r₁ := b2e354
             have r₂ := b2e22
             grind)
          | exact resolve b2e354 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e354
        have b2e366 : (σ (M.op y x)) ≠ (M.op (σ (M.op y x)) (σ y)) := by
          first
          | (have i₁ := b2e363
             have i₂ := b2e39
             grind)
          | exact superpose b2e39 b2e363
          | exact resolve b2e363 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39 b2e363
        have b2e464 : (σ (M.op y x)) ≠ (σ (M.op y x)) ∨ (σ (M.op y x)) = (M.op (σ (M.op y x)) (σ y)) := by
          first
          | (have i₁ := b2e361 (M.op y x) y
             have i₂ := b2e42
             grind)
          | exact superpose b2e42 b2e361
          | (have j0 := b2e361 (M.op y x) y
             grind)
          | exact resolve b2e361 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e42 b2e361
        have b2e468 : (σ (M.op y x)) = (M.op (σ (M.op y x)) (σ y)) := by grind
        clear b2e464
        have b2e471 : False := by grind
        exact b2e471
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ y) (σ x)) (σ y)) (M.op (σ y) (σ x)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op X1 X0) X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (M.op (M.op X1 X0) X1) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : (M.op y x) ≠ (M.op (M.op y x) y) := by grind
        have b3e21 : y = (M.op y x) := by grind
        have b3e22 : (M.op (σ y) (σ x)) = (M.op (M.op (σ y) (σ x)) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : y ≠ (M.op y y) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e20
          | exact resolve b3e20 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e39 : (M.op (σ y) (σ x)) ≠ (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) ∨ (M.op (σ y) (σ x)) = (k (σ y) (M.op (σ y) (σ x))) := by
          first
          | (have i₁ := b3e15 (σ y) (M.op (σ y) (σ x))
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e15
          | (have r₁ := b3e15 (σ x) (σ y)
             have r₂ := b3e22
             grind)
          | exact resolve b3e15 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e40 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
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
        have b3e41 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b3e40
        have b3e42 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e41
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e41
          | exact resolve b3e41 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e41
        have b3e45 : y ≠ y ∨ y = (M.op y y) ∨ y = (k x y) := by
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
        have b3e46 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) ∨ (M.op (σ y) (σ x)) = (k (σ y) (M.op (σ y) (σ x))) := by
          first
          | (have i₁ := b3e16 (σ y) (M.op (σ y) (σ x))
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e16
          | (have j0 := b3e16 (σ y) (M.op (σ y) (σ x))
             grind)
          | (have r₁ := b3e16 (σ y) (M.op (σ y) (σ x))
             have r₂ := b3e22
             grind)
          | exact resolve b3e16 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e48 : (M.op (σ y) (σ x)) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) ∨ (M.op (σ y) (σ x)) = (k (σ y) (M.op (σ y) (σ x))) := by grind
        clear b3e46
        have b3e49 : y = (M.op y y) ∨ y = (k x y) := by grind
        clear b3e45
        have b3e50 : (M.op (σ y) (σ x)) = (k (σ y) (M.op (σ y) (σ x))) := by
          first
          | (have r₁ := b3e48
             have r₂ := b3e39
             grind)
          | exact resolve b3e48 b3e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39 b3e48
        have b3e51 : y = (k x y) := by
          first
          | (have r₁ := b3e49
             have r₂ := b3e23
             grind)
          | exact resolve b3e49 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49
        have b3e52 : (σ (k x y)) = (k (σ y) (σ (k x y))) := by
          first
          | (have i₁ := b3e50
             have i₂ := b3e42
             grind)
          | exact superpose b3e42 b3e50
          | exact resolve b3e50 b3e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42 b3e50
        have b3e53 : (σ (k x y)) = (σ (k y (k x y))) := by
          first
          | (have i₁ := b3e52
             have i₂ := b3e18 y (k x y)
             grind)
          | exact superpose b3e18 b3e52
          | exact resolve b3e52 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52
        have b3e54 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b3e53
             have i₂ := b3e51
             grind)
          | exact superpose b3e51 b3e53
          | exact resolve b3e53 b3e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e51 b3e53
        have b3e56 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e15 X1 X0
             have i₂ := b3e17 X1 X0
             grind)
          | exact superpose b3e17 b3e15
          | (have j0 := b3e15 X1 X0
             have j1 := b3e17 X1 X0
             grind)
          | (have r₁ := b3e15 X0 X1
             have r₂ := b3e17 X0 X1
             grind)
          | (have r₁ := b3e15 X0 X0
             have r₂ := b3e17 X0 (M.op X0 X0)
             grind)
          | exact resolve b3e15 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e60 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b3e56 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e56
        have b3e61 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b3e60 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e60
        have b3e65 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (k y y)
             have i₂ := b3e54
             grind)
          | exact superpose b3e54 b3e13
          | exact resolve b3e13 b3e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54
        have b3e66 : y = (k y y) := by
          first
          | (have i₁ := b3e65
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e65
          | exact resolve b3e65 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e65
        have b3e80 : y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e61 y y
             have i₂ := b3e66
             grind)
          | exact superpose b3e66 b3e61
          | (have j0 := b3e61 y y
             grind)
          | exact resolve b3e61 b3e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e61 b3e66
        have b3e81 : y = (M.op y y) := by grind
        clear b3e80
        have b3e83 : False := by grind
        exact b3e83
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op X1 X0) X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (M.op (M.op X1 X0) X1) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
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
          have b4e50 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X1 X0
               have i₂ := b4e18 X1 X0
               grind)
            | exact superpose b4e18 b4e16
            | (have j0 := b4e16 X1 X0
               have j1 := b4e18 X1 X0
               grind)
            | (have r₁ := b4e16 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e16 X0 X0
               have r₂ := b4e18 X0 (M.op X0 X0)
               grind)
            | exact resolve b4e16 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e54 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e50 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e50
          have b4e55 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e54 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54
          have b4e69 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 X0
               have i₂ := b4e55 (σ X0) (σ X1)
               grind)
            | exact superpose b4e55 b4e19
            | (have j1 := b4e55 (σ X0) (σ X1)
               grind)
            | exact resolve b4e19 b4e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e70 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e27 X1 X0
               have i₂ := b4e55 X0 (τ X1)
               grind)
            | exact superpose b4e55 b4e27
            | (have j1 := b4e55 X0 (τ X1)
               grind)
            | exact resolve b4e27 b4e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27 b4e55
          have b4e183 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e70 X0 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e70
            | exact resolve b4e70 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e70
          have b4e206 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e183 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e183
            | (have j0 := b4e183 X0 X1
               grind)
            | exact resolve b4e183 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e183
          have b4e323 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e69 x y
               grind)
            | exact superpose b4e69 b4e20
            | (have j1 := b4e69 x y
               grind)
            | exact resolve b4e20 b4e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e328 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e69 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e69
          have b4e552 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e323
               have i₂ := b4e206 y x
               grind)
            | exact superpose b4e206 b4e323
            | (have j1 := b4e206 (σ y) (σ x)
               grind)
            | (have r₁ := b4e323
               have r₂ := b4e206 y x
               grind)
            | exact resolve b4e323 b4e206
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e323
          have b4e553 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
          clear b4e552
          have b4e556 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e553
               grind)
            | exact superpose b4e553 b4e20
            | exact resolve b4e20 b4e553
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e557 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e17 (σ y) (σ x)
               have i₂ := b4e553
               grind)
            | exact superpose b4e553 b4e17
            | (have j0 := b4e17 (σ y) (σ x)
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e553
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e553
               grind)
            | exact resolve b4e17 b4e553
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e558 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e16 (σ y) (σ x)
               have i₂ := b4e553
               grind)
            | exact superpose b4e553 b4e16
            | exact resolve b4e16 b4e553
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e553
          have b4e559 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b4e557
          have b4e560 : (σ x) = (σ (k y x)) ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e558
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e558
            | exact resolve b4e558 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e558
          have b4e561 : (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e559
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e559
            | exact resolve b4e559 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e559
          have b4e563 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e561
               have r₂ := b4e560
               grind)
            | exact resolve b4e561 b4e560
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e560 b4e561
          have b4e698 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e206 y x
               have i₂ := b4e563
               grind)
            | exact superpose b4e563 b4e206
            | (have j0 := b4e206 y x
               grind)
            | exact resolve b4e206 b4e563
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e206 b4e563
          have b4e722 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
          clear b4e698
          have b4e743 : x = (M.op x y) := by
            first
            | (have r₁ := b4e722
               have r₂ := b4e556
               grind)
            | exact resolve b4e722 b4e556
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e556 b4e722
          have b4e824 : x ≠ x ∨ x = (M.op x x) ∨ x = (k y x) := by
            first
            | (have i₁ := b4e17 y x
               have i₂ := b4e743
               grind)
            | exact superpose b4e743 b4e17
            | (have j0 := b4e17 y x
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e743
               grind)
            | exact resolve b4e17 b4e743
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e825 : x ≠ (M.op x x) ∨ x = (k y x) := by
            first
            | (have i₁ := b4e16 y x
               have i₂ := b4e743
               grind)
            | exact superpose b4e743 b4e16
            | exact resolve b4e16 b4e743
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e826 : x = (M.op x x) ∨ x = (k y x) := by grind
          clear b4e824
          have b4e827 : x = (k y x) := by
            first
            | (have r₁ := b4e826
               have r₂ := b4e825
               grind)
            | exact resolve b4e826 b4e825
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e825 b4e826
          have b4e912 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e328 x y
               have i₂ := b4e827
               grind)
            | exact superpose b4e827 b4e328
            | (have j0 := b4e328 x y
               grind)
            | exact resolve b4e328 b4e827
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e328 b4e827
          have b4e916 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b4e912
          have b4e1007 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e916
               grind)
            | exact superpose b4e916 b4e20
            | exact resolve b4e20 b4e916
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e916
          have b4e1013 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e1007
               have i₂ := b4e743
               grind)
            | exact superpose b4e743 b4e1007
            | exact resolve b4e1007 b4e743
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e743 b4e1007
          have b4e1014 : False := by grind
          exact b4e1014
        · have b5e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op X1 X0) X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (M.op (M.op X1 X0) X1) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op y x) ≠ (M.op (M.op y x) y) := by grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : y ≠ (M.op y y) := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e21
            | exact resolve b5e21 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e41 : y ≠ y ∨ y = (M.op y y) ∨ y = (k x y) := by
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
          have b5e42 : y = (M.op y y) ∨ y = (k x y) := by grind
          clear b5e41
          have b5e43 : y = (k x y) := by
            first
            | (have r₁ := b5e42
               have r₂ := b5e25
               grind)
            | exact resolve b5e42 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e42
          have b5e45 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
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
            | (have r₁ := b5e16 X0 X0
               have r₂ := b5e18 X0 (M.op X0 X0)
               grind)
            | exact resolve b5e16 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e49 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e45 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45
          have b5e50 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e49 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49
          have b5e65 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X1 X0
               have i₂ := b5e50 (σ X0) (σ X1)
               grind)
            | exact superpose b5e50 b5e19
            | (have j1 := b5e50 (σ X0) (σ X1)
               grind)
            | exact resolve b5e19 b5e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50
          have b5e324 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e65 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e65
          have b5e464 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e324 y x
               have i₂ := b5e43
               grind)
            | exact superpose b5e43 b5e324
            | (have j0 := b5e324 y x
               grind)
            | exact resolve b5e324 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43 b5e324
          have b5e468 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear b5e464
          have b5e471 : False := by grind
          exact b5e471
    · rcases eq_or_ne (M.op (M.op (σ y) (σ x)) (σ y)) (M.op (σ y) (σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op X1 X0) X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (M.op (M.op X1 X0) X1) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op y x) ≠ (M.op (M.op y x) y) := by grind
        have b6e21 : y ≠ (M.op y x) := by grind
        have b6e22 : (M.op (σ y) (σ x)) = (M.op (M.op (σ y) (σ x)) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e37 : (M.op (σ y) (σ x)) ≠ (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) ∨ (M.op (σ y) (σ x)) = (k (σ y) (M.op (σ y) (σ x))) := by
          first
          | (have i₁ := b6e15 (σ y) (M.op (σ y) (σ x))
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e15
          | (have r₁ := b6e15 (σ x) (σ y)
             have r₂ := b6e22
             grind)
          | exact resolve b6e15 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e38 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
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
        have b6e39 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b6e38
        have b6e40 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e39
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e39
          | exact resolve b6e39 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e39
        have b6e43 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) ∨ (M.op (σ y) (σ x)) = (k (σ y) (M.op (σ y) (σ x))) := by
          first
          | (have i₁ := b6e16 (σ y) (M.op (σ y) (σ x))
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e16
          | (have j0 := b6e16 (σ y) (M.op (σ y) (σ x))
             grind)
          | (have r₁ := b6e16 (σ y) (M.op (σ y) (σ x))
             have r₂ := b6e22
             grind)
          | exact resolve b6e16 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e45 : (M.op (σ y) (σ x)) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) ∨ (M.op (σ y) (σ x)) = (k (σ y) (M.op (σ y) (σ x))) := by grind
        clear b6e43
        have b6e46 : (M.op (σ y) (σ x)) = (k (σ y) (M.op (σ y) (σ x))) := by
          first
          | (have r₁ := b6e45
             have r₂ := b6e37
             grind)
          | exact resolve b6e45 b6e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e37 b6e45
        have b6e47 : (σ (k x y)) = (k (σ y) (σ (k x y))) := by
          first
          | (have i₁ := b6e46
             have i₂ := b6e40
             grind)
          | exact superpose b6e40 b6e46
          | exact resolve b6e46 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40 b6e46
        have b6e48 : (σ (k x y)) = (σ (k y (k x y))) := by
          first
          | (have i₁ := b6e47
             have i₂ := b6e18 y (k x y)
             grind)
          | exact superpose b6e18 b6e47
          | exact resolve b6e47 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e47
        have b6e59 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
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
          | (have r₁ := b6e15 X0 X0
             have r₂ := b6e17 X0 (M.op X0 X0)
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e63 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e59 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e59
        have b6e64 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e63 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e63
        have b6e83 : (k y (k x y)) = (τ (σ (k x y))) := by
          first
          | (have i₁ := b6e13 (k y (k x y))
             have i₂ := b6e48
             grind)
          | exact superpose b6e48 b6e13
          | exact resolve b6e13 b6e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e48
        have b6e84 : (k x y) = (k y (k x y)) := by
          first
          | (have i₁ := b6e83
             have i₂ := b6e13 (k x y)
             grind)
          | exact superpose b6e13 b6e83
          | exact resolve b6e83 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e83
        have b6e98 : (k x y) = (M.op (k x y) y) ∨ (k x y) = (M.op (k x y) y) := by
          first
          | (have i₁ := b6e84
             have i₂ := b6e64 (k x y) y
             grind)
          | exact superpose b6e64 b6e84
          | (have j1 := b6e64 (k x y) y
             grind)
          | exact resolve b6e84 b6e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e84
        have b6e100 : (k x y) = (M.op (k x y) y) := by grind
        clear b6e98
        have b6e104 : (M.op y x) = (M.op (M.op y x) y) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b6e100
             have i₂ := b6e64 y x
             grind)
          | exact superpose b6e64 b6e100
          | (have j1 := b6e64 (M.op y x) y
             grind)
          | exact resolve b6e100 b6e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64 b6e100
        have b6e108 : y = (M.op y x) := by
          first
          | (have r₁ := b6e104
             have r₂ := b6e20
             grind)
          | exact resolve b6e104 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e104
        have b6e109 : False := by grind
        exact b6e109
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op X1 X0) X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (M.op (M.op X1 X0) X1) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op y x) := by grind
          have b7e23 : (M.op (σ y) (σ x)) ≠ (M.op (M.op (σ y) (σ x)) (σ y)) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (σ y) ≠ (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e41 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e42 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e41
          have b7e43 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e42
               have r₂ := b7e25
               grind)
            | exact resolve b7e42 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e42
          have b7e44 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e43
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e43
            | exact resolve b7e43 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e43
          have b7e47 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e44
               grind)
            | exact superpose b7e44 b7e14
            | exact resolve b7e14 b7e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e48 : y = (k x y) := by
            first
            | (have i₁ := b7e47
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e47
            | exact resolve b7e47 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
          have b7e52 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
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
            | (have r₁ := b7e16 X0 X0
               have r₂ := b7e18 X0 (M.op X0 X0)
               grind)
            | exact resolve b7e16 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e56 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e52 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
          have b7e57 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e56 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e65 : y = (M.op y x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e48
               have i₂ := b7e57 y x
               grind)
            | exact superpose b7e57 b7e48
            | (have j1 := b7e57 y x
               grind)
            | exact resolve b7e48 b7e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48 b7e57
          have b7e67 : y = (M.op y x) := by grind
          clear b7e65
          have b7e70 : False := by grind
          exact b7e70
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op (M.op X1 X0) X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (M.op (M.op X1 X0) X1) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b8e49 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
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
            | (have r₁ := b8e16 X0 X0
               have r₂ := b8e18 X0 (M.op X0 X0)
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e53 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e49 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e49
          have b8e54 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e53 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e53
          have b8e71 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e54 (σ X0) (σ X1)
               grind)
            | exact superpose b8e54 b8e19
            | (have j1 := b8e54 (σ X0) (σ X1)
               grind)
            | exact resolve b8e19 b8e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e73 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e25 X1 X0
               have i₂ := b8e54 X0 (τ X1)
               grind)
            | exact superpose b8e54 b8e25
            | (have j1 := b8e54 X0 (τ X1)
               grind)
            | exact resolve b8e25 b8e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25 b8e54
          have b8e200 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e73 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e73
            | exact resolve b8e73 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e73
          have b8e225 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e200 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e200
            | (have j0 := b8e200 X0 X1
               grind)
            | exact resolve b8e200 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e200
          have b8e349 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e71 x y
               grind)
            | exact superpose b8e71 b8e20
            | (have j1 := b8e71 x y
               grind)
            | exact resolve b8e20 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e354 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e71 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e71
          have b8e532 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e349
               have i₂ := b8e225 y x
               grind)
            | exact superpose b8e225 b8e349
            | (have j1 := b8e225 (σ y) (σ x)
               grind)
            | (have r₁ := b8e349
               have r₂ := b8e225 y x
               grind)
            | exact resolve b8e349 b8e225
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e349
          have b8e533 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
          clear b8e532
          have b8e536 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e533
               grind)
            | exact superpose b8e533 b8e20
            | exact resolve b8e20 b8e533
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e537 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e533
               grind)
            | exact superpose b8e533 b8e17
            | (have j0 := b8e17 (σ y) (σ x)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e533
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e533
               grind)
            | exact resolve b8e17 b8e533
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e538 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e16 (σ y) (σ x)
               have i₂ := b8e533
               grind)
            | exact superpose b8e533 b8e16
            | exact resolve b8e16 b8e533
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e533
          have b8e539 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b8e537
          have b8e540 : (σ x) = (σ (k y x)) ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e538
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e538
            | exact resolve b8e538 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e538
          have b8e541 : (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e539
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e539
            | exact resolve b8e539 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e539
          have b8e543 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e541
               have r₂ := b8e540
               grind)
            | exact resolve b8e541 b8e540
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e540 b8e541
          have b8e676 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e225 y x
               have i₂ := b8e543
               grind)
            | exact superpose b8e543 b8e225
            | (have j0 := b8e225 y x
               grind)
            | exact resolve b8e225 b8e543
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e225 b8e543
          have b8e699 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
          clear b8e676
          have b8e720 : x = (M.op x y) := by
            first
            | (have r₁ := b8e699
               have r₂ := b8e536
               grind)
            | exact resolve b8e699 b8e536
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e536 b8e699
          have b8e800 : x ≠ x ∨ x = (M.op x x) ∨ x = (k y x) := by
            first
            | (have i₁ := b8e17 y x
               have i₂ := b8e720
               grind)
            | exact superpose b8e720 b8e17
            | (have j0 := b8e17 y x
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e720
               grind)
            | exact resolve b8e17 b8e720
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e801 : x ≠ (M.op x x) ∨ x = (k y x) := by
            first
            | (have i₁ := b8e16 y x
               have i₂ := b8e720
               grind)
            | exact superpose b8e720 b8e16
            | exact resolve b8e16 b8e720
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e802 : x = (M.op x x) ∨ x = (k y x) := by grind
          clear b8e800
          have b8e803 : x = (k y x) := by
            first
            | (have r₁ := b8e802
               have r₂ := b8e801
               grind)
            | exact resolve b8e802 b8e801
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e801 b8e802
          have b8e887 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e354 x y
               have i₂ := b8e803
               grind)
            | exact superpose b8e803 b8e354
            | (have j0 := b8e354 x y
               grind)
            | exact resolve b8e354 b8e803
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e354 b8e803
          have b8e891 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b8e887
          have b8e981 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e891
               grind)
            | exact superpose b8e891 b8e20
            | exact resolve b8e20 b8e891
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e891
          have b8e987 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b8e981
               have i₂ := b8e720
               grind)
            | exact superpose b8e720 b8e981
            | exact resolve b8e981 b8e720
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e720 b8e981
          have b8e988 : False := by grind
          exact b8e988

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(Y,X),Y) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppyxy_x_x_y_pxy_pxx_pxy_Equation1 :
    AutBox.GuardAut2 (((Lf 1) ⋆ (Lf 0)) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 1) ⋆ (Lf 0)) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op b a) b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op b a) b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op b a) b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op (M.op b a) b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op b a) b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op b a) b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op y x) y) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ y) (σ x)) (σ y)) ((σ x)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op (M.op y x) y) := by grind
      have b0e20 : (σ x) = (M.op (M.op (σ y) (σ x)) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e30 : x ≠ x ∨ (M.op x y) = (k x y) := by
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
      have b0e31 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b1e15 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : x = (M.op (M.op y x) y) := by grind
        have b1e21 : (σ x) ≠ (M.op (M.op (σ y) (σ x)) (σ y)) := by grind
        have b1e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (σ x) ≠ (M.op (M.op (σ x) (σ x)) (σ x)) := by
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
        have b1e28 : x = (M.op (M.op x x) x) := by
          first
          | (have i₁ := b1e20
             have i₂ := b1e27
             grind)
          | exact superpose b1e27 b1e20
          | exact resolve b1e20 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e50 : x ≠ x ∨ (M.op x x) = (k x x) := by
          first
          | (have i₁ := b1e15 x x
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e15
          | (have j0 := b1e15 x x
             grind)
          | (have r₁ := b1e15 x x
             have r₂ := b1e28
             grind)
          | exact resolve b1e15 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28
        have b1e51 : (M.op x x) = (k x x) := by grind
        clear b1e50
        have b1e57 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by grind
        clear b1e24
        have b1e59 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by grind
        clear b1e57
        have b1e62 : (M.op (σ x) (σ x)) = (σ (k x x)) := by
          first
          | (have i₁ := b1e59
             have i₂ := b1e18 x x
             grind)
          | exact superpose b1e18 b1e59
          | exact resolve b1e59 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59
        have b1e63 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e62
             have i₂ := b1e51
             grind)
          | exact superpose b1e51 b1e62
          | exact resolve b1e62 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51 b1e62
        have b1e85 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e25
             have i₂ := b1e63
             grind)
          | exact superpose b1e63 b1e25
          | exact resolve b1e25 b1e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e63
        have b1e90 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e85
             have i₂ := b1e27
             grind)
          | exact superpose b1e27 b1e85
          | exact resolve b1e85 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27 b1e85
        have b1e91 : False := by grind
        exact b1e91
      · have b2e15 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : x = (M.op (M.op y x) y) := by grind
        have b2e22 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e39 : x ≠ x ∨ (M.op x y) = (k x y) := by
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
        have b2e59 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
          | (have r₁ := b2e15 X1 X1
             have r₂ := b2e17 (M.op (M.op X1 X1) X1) X1
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 (M.op (M.op X1 X0) X1)
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e61 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e59 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e59
        have b2e62 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e61 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61
        have b2e67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e62 (σ X0) (σ X1)
             grind)
          | exact superpose b2e62 b2e18
          | (have j1 := b2e62 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
             grind)
          | exact resolve b2e18 b2e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e62
        have b2e473 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e67 x y
             grind)
          | exact superpose b2e67 b2e19
          | (have j1 := b2e67 x y
             grind)
          | exact resolve b2e19 b2e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e67
        have b2e487 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e473
             have r₂ := b2e22
             grind)
          | exact resolve b2e473 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e473
        have b2e492 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b2e487
             have i₂ := b2e40
             grind)
          | exact superpose b2e40 b2e487
          | exact resolve b2e487 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40 b2e487
        have b2e493 : False := by grind
        exact b2e493
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ y) (σ x)) (σ y)) ((σ x)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : x ≠ (M.op (M.op y x) y) := by grind
        have b3e21 : x = y := by grind
        have b3e22 : (σ x) = (M.op (M.op (σ y) (σ x)) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e34 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by grind
        have b3e35 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by grind
        clear b3e34
        have b3e36 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e35
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e35
          | exact resolve b3e35 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e35
        have b3e47 : y ≠ y ∨ (M.op y y) = (k y y) := by grind
        have b3e48 : (M.op y y) = (k y y) := by grind
        clear b3e47
        have b3e71 : (σ (M.op y y)) ≠ (σ (k y y)) := by grind
        clear b3e36
        have b3e74 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e71
             have i₂ := b3e48
             grind)
          | exact superpose b3e48 b3e71
          | exact resolve b3e71 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48 b3e71
        have b3e75 : False := by grind
        exact b3e75
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e17 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ (M.op (M.op y x) y) := by grind
          have b4e22 : x = y := by grind
          have b4e23 : (σ x) ≠ (M.op (M.op (σ y) (σ x)) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e46 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by grind
          have b4e47 : y ≠ y ∨ (M.op y y) = (k y y) := by grind
          have b4e48 : (M.op y y) = (k y y) := by grind
          clear b4e47
          have b4e49 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b4e46
          have b4e52 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b4e49
               have i₂ := b4e19 y y
               grind)
            | exact superpose b4e19 b4e49
            | exact resolve b4e49 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49
          have b4e53 : (σ (M.op y y)) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b4e52
               have i₂ := b4e48
               grind)
            | exact superpose b4e48 b4e52
            | exact resolve b4e52 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48 b4e52
          have b4e54 : False := by grind
          exact b4e54
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (M.op (σ y) (σ x)) (σ y)) ((σ x)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e21 : x ≠ y := by grind
        have b6e22 : (σ x) = (M.op (M.op (σ y) (σ x)) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e39 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b6e42 : (σ (M.op x y)) ≠ (σ (k x y)) := by
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
        have b6e64 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
          | (have r₁ := b6e15 X1 X1
             have r₂ := b6e17 (M.op (M.op X1 X1) X1) X1
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 X0 (M.op (M.op X1 X0) X1)
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e66 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e64 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64
        have b6e67 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e66 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e66
        have b6e74 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
          first
          | (have i₁ := b6e42
             have i₂ := b6e67 x y
             grind)
          | exact superpose b6e67 b6e42
          | (have j1 := b6e67 x y
             grind)
          | (have r₁ := b6e42
             have r₂ := b6e67 (σ (M.op x y)) (σ (k x y))
             grind)
          | (have r₁ := b6e42
             have r₂ := b6e67 (σ (k x y)) (σ (M.op x y))
             grind)
          | exact resolve b6e42 b6e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42 b6e67
        have b6e75 : x = y := by grind
        clear b6e74
        have b6e76 : False := by grind
        exact b6e76
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
          have b8e16 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
          have b8e58 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
            | (have r₁ := b8e16 X1 X1
               have r₂ := b8e18 (M.op (M.op X1 X1) X1) X1
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 (M.op (M.op X1 X0) X1)
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e60 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e58 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e58
          have b8e61 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e60 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60
          have b8e66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e61 (σ X0) (σ X1)
               grind)
            | exact superpose b8e61 b8e19
            | (have j1 := b8e61 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
               grind)
            | exact resolve b8e19 b8e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e67 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X0 X1
               have i₂ := b8e61 (τ X0) X1
               grind)
            | exact superpose b8e61 b8e26
            | (have j1 := b8e61 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
               grind)
            | exact resolve b8e26 b8e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e61
          have b8e127 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e67 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e67
            | exact resolve b8e67 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e67
          have b8e143 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e127 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e127
            | (have j0 := b8e127 (σ (k X0 X1)) (σ (M.op X0 X1))
               grind)
            | exact resolve b8e127 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e127
          have b8e471 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e66 x y
               grind)
            | exact superpose b8e66 b8e20
            | (have j1 := b8e66 x y
               grind)
            | exact resolve b8e20 b8e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66
          have b8e485 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e471
               have r₂ := b8e24
               grind)
            | exact resolve b8e471 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e471
          have b8e493 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
            first
            | (have i₁ := b8e485
               have i₂ := b8e143 x y
               grind)
            | exact superpose b8e143 b8e485
            | (have j1 := b8e143 x y
               grind)
            | (have r₁ := b8e485
               have r₂ := b8e143 x y
               grind)
            | (have r₁ := b8e485
               have r₂ := b8e143 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e485
               have r₂ := b8e143 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e485 b8e143
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e143 b8e485
          have b8e494 : x = y := by grind
          clear b8e493
          have b8e496 : False := by grind
          exact b8e496

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(Y,Y),m(Y,Y)) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppyypyy_x_pxy_y_pxy_y_pxy_Equation1 :
    AutBox.GuardAut2 (((Lf 1) ⋆ (Lf 1)) ⋆ ((Lf 1) ⋆ (Lf 1))) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 1) ⋆ (Lf 1)) ⋆ ((Lf 1) ⋆ (Lf 1))) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op b b) (M.op b b) ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op b b) (M.op b b)) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op b b) (M.op b b) = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op (M.op b b) (M.op b b)) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op b b) (M.op b b) = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op b b) (M.op b b)) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op y y) (M.op y y)) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ((σ x)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X1 X1)) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op (M.op y y) (M.op y y)) := by grind
      have b0e20 : (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e40 : (M.op x y) = (k x y) := by grind
      have b0e41 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
      have b0e43 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e41
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e41
        | exact resolve b0e41 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41
      have b0e44 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e43
           have i₂ := b0e40
           grind)
        | exact superpose b0e40 b0e43
        | exact resolve b0e43 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40 b0e43
      have b0e45 : False := by grind
      exact b0e45
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X1 X1)) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op (M.op X1 X1) (M.op X1 X1)) = X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : x = (M.op (M.op y y) (M.op y y)) := by grind
        have b1e21 : (σ x) ≠ (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e19
          | exact resolve b1e19 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e39 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e41 : (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e39
        have b1e42 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e41
             have r₂ := b1e21
             grind)
          | exact resolve b1e41 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41
        have b1e43 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e42
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e42
          | exact resolve b1e42 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42
        have b1e46 : (k x y) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (k x y)
             have i₂ := b1e43
             grind)
          | exact superpose b1e43 b1e13
          | exact resolve b1e13 b1e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43
        have b1e47 : y = (k x y) := by
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
        have b1e51 : (M.op x y) = (k x y) := by grind
        have b1e53 : y = (M.op x y) := by
          first
          | (have i₁ := b1e51
             have i₂ := b1e47
             grind)
          | exact superpose b1e47 b1e51
          | exact resolve b1e51 b1e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47 b1e51
        have b1e54 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e24
             have i₂ := b1e53
             grind)
          | exact superpose b1e53 b1e24
          | exact resolve b1e24 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e53
        have b1e57 : False := by grind
        exact b1e57
      · have b2e15 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X1 X1)) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X1 X1)) = X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : x = (M.op (M.op y y) (M.op y y)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e48 : (M.op x y) = (k x y) := by grind
        have b2e58 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e65 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e58 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e58
        have b2e82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e65 (σ X0) (σ X1)
             grind)
          | exact superpose b2e65 b2e18
          | (have j1 := b2e65 (σ X0) (σ X1)
             grind)
          | exact resolve b2e18 b2e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e65
        have b2e455 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e82 x y
             grind)
          | exact superpose b2e82 b2e19
          | (have j1 := b2e82 x y
             grind)
          | exact resolve b2e19 b2e82
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e82
        have b2e466 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e455
             have r₂ := b2e22
             grind)
          | exact resolve b2e455 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e455
        have b2e469 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b2e466
             have i₂ := b2e48
             grind)
          | exact superpose b2e48 b2e466
          | exact resolve b2e466 b2e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48 b2e466
        have b2e470 : False := by grind
        exact b2e470
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ((σ x)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X1 X1)) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op (M.op X1 X1) (M.op X1 X1)) = X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : x ≠ (M.op (M.op y y) (M.op y y)) := by grind
        have b3e21 : y = (M.op x y) := by grind
        have b3e22 : (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e19
          | exact resolve b3e19 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e39 : y ≠ y ∨ x = (M.op (M.op y y) (M.op y y)) ∨ y = (k x y) := by
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
        have b3e41 : x = (M.op (M.op y y) (M.op y y)) ∨ y = (k x y) := by grind
        clear b3e39
        have b3e42 : y = (k x y) := by
          first
          | (have r₁ := b3e41
             have r₂ := b3e20
             grind)
          | exact resolve b3e41 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e41
        have b3e44 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        have b3e46 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e44
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e44
          | exact resolve b3e44 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44
        have b3e47 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e46
             have i₂ := b3e42
             grind)
          | exact superpose b3e42 b3e46
          | exact resolve b3e46 b3e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42 b3e46
        have b3e48 : False := by grind
        exact b3e48
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x y) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e26 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e27 : (σ y) ≠ (σ y) := by
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
          have b4e28 : False := by grind
          exact b4e28
        · have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op (M.op X1 X1) (M.op X1 X1)) = X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X1 X1)) = X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ (M.op (M.op y y) (M.op y y)) := by grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e23 : (σ x) ≠ (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e41 : y ≠ y ∨ x = (M.op (M.op y y) (M.op y y)) ∨ y = (k x y) := by
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
          have b5e42 : x = (M.op (M.op y y) (M.op y y)) ∨ y = (k x y) := by grind
          clear b5e41
          have b5e43 : y = (k x y) := by
            first
            | (have r₁ := b5e42
               have r₂ := b5e21
               grind)
            | exact resolve b5e42 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42
          have b5e64 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X1) (σ X1)) (M.op (σ X1) (σ X1))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e162 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (M.op (σ X1) (σ X1)) (M.op (σ X1) (σ X1))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e64 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e64
          have b5e664 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e162 x y
               have i₂ := b5e43
               grind)
            | exact superpose b5e43 b5e162
            | (have j0 := b5e162 x y
               grind)
            | exact resolve b5e162 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43 b5e162
          have b5e669 : (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b5e664
          have b5e672 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e669
               have r₂ := b5e23
               grind)
            | exact resolve b5e669 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e669
          have b5e676 : False := by grind
          exact b5e676
    · rcases eq_or_ne (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ((σ x)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X1 X1)) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X1 X1)) = X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e21 : y ≠ (M.op x y) := by grind
        have b6e22 : (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e48 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        have b6e51 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e48
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e48
          | exact resolve b6e48 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e48
        have b6e52 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e51
             grind)
          | exact superpose b6e51 b6e19
          | exact resolve b6e19 b6e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51
        have b6e61 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e68 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e61 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e61
        have b6e74 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e52
             have i₂ := b6e68 x y
             grind)
          | exact superpose b6e68 b6e52
          | (have j1 := b6e68 x y
             grind)
          | exact resolve b6e52 b6e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e52 b6e68
        have b6e75 : y = (M.op x y) := by grind
        clear b6e74
        have b6e76 : False := by grind
        exact b6e76
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X1 X1)) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op (M.op X1 X1) (M.op X1 X1)) = X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X1 X1)) = X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (σ x) ≠ (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e33 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e34 : (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e33
          have b7e35 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e34
               have r₂ := b7e23
               grind)
            | exact resolve b7e34 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e36 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e35
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e35
            | exact resolve b7e35 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35
          have b7e39 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e36
               grind)
            | exact superpose b7e36 b7e14
            | exact resolve b7e14 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36
          have b7e40 : y = (k x y) := by
            first
            | (have i₁ := b7e39
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e39
            | exact resolve b7e39 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39
          have b7e48 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e53 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e48 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e69 : y = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e40
               have i₂ := b7e53 x y
               grind)
            | exact superpose b7e53 b7e40
            | (have j1 := b7e53 x y
               grind)
            | exact resolve b7e40 b7e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40 b7e53
          have b7e71 : y = (M.op x y) := by grind
          clear b7e69
          have b7e74 : False := by grind
          exact b7e74
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X1 X1)) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X1 X1)) = X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : y ≠ (M.op x y) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
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
          have b8e55 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e62 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e55 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55
          have b8e79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e62 (σ X0) (σ X1)
               grind)
            | exact superpose b8e62 b8e19
            | (have j1 := b8e62 (σ X0) (σ X1)
               grind)
            | exact resolve b8e19 b8e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e81 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X0 X1
               have i₂ := b8e62 (τ X0) X1
               grind)
            | exact superpose b8e62 b8e26
            | (have j1 := b8e62 (τ X0) X1
               grind)
            | exact resolve b8e26 b8e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e62
          have b8e281 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e81 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e81
            | exact resolve b8e81 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e81
          have b8e311 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e281 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e281
            | (have j0 := b8e281 X0 X1
               grind)
            | exact resolve b8e281 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e281
          have b8e449 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e79 x y
               grind)
            | exact superpose b8e79 b8e20
            | (have j1 := b8e79 x y
               grind)
            | exact resolve b8e20 b8e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e79
          have b8e460 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e449
               have r₂ := b8e24
               grind)
            | exact resolve b8e449 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e449
          have b8e464 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e460
               have i₂ := b8e311 x y
               grind)
            | exact superpose b8e311 b8e460
            | (have j1 := b8e311 x y
               grind)
            | (have r₁ := b8e460
               have r₂ := b8e311 x y
               grind)
            | exact resolve b8e460 b8e311
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e311 b8e460
          have b8e465 : y = (M.op x y) := by grind
          clear b8e464
          have b8e467 : False := by grind
          exact b8e467

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(m(Y,Y),Y) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_ppyyy_y_pxy_x_pxy_x_pxy_Equation1 :
    AutBox.GuardAut2 (((Lf 1) ⋆ (Lf 1)) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of (((Lf 1) ⋆ (Lf 1)) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op (M.op b b) b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op b b) b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op (M.op b b) b = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op (M.op b b) b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op (M.op b b) b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op (M.op b b) b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op (M.op y y) y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (M.op (σ y) (σ y)) (σ y)) ((σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op (M.op y y) y) := by grind
      have b0e20 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e27 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e14 X0 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 X0 y
           grind)
        | (have r₁ := b0e14 X0 y
           have r₂ := b0e19
           grind)
        | exact resolve b0e14 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e28 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e14 X0 (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have j0 := b0e14 X0 (σ y)
           grind)
        | (have r₁ := b0e14 X0 (σ y)
           have r₂ := b0e20
           grind)
        | exact resolve b0e14 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e29 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have j0 := b0e28 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28
      have b0e30 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
        intro X0
        first
        | (have j0 := b0e27 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27
      have b0e34 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 y
           have i₂ := b0e29 (σ X0)
           grind)
        | exact superpose b0e29 b0e17
        | exact resolve b0e17 b0e29
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29
      have b0e36 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
        intro X0
        first
        | (have i₁ := b0e34 X0
           have i₂ := b0e30 X0
           grind)
        | exact superpose b0e30 b0e34
        | exact resolve b0e34 b0e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30 b0e34
      have b0e108 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e36 x
           grind)
        | exact superpose b0e36 b0e18
        | (have r₁ := b0e18
           have r₂ := b0e36 x
           grind)
        | exact resolve b0e18 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36
      have b0e115 : False := by grind
      exact b0e115
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op (M.op X1 X1) X1) = X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op (M.op y y) y) := by grind
        have b1e21 : (σ y) ≠ (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
        have b1e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e19
          | exact resolve b1e19 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e38 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e15 X0 y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e15
          | (have j0 := b1e15 X0 y
             grind)
          | (have r₁ := b1e15 X0 y
             have r₂ := b1e20
             grind)
          | exact resolve b1e15 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e39 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
          intro X0
          first
          | (have j0 := b1e38 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38
        have b1e41 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e42 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e41
        have b1e43 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e42
             have r₂ := b1e21
             grind)
          | exact resolve b1e42 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42
        have b1e44 : (σ x) = (σ (k x y)) := by
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
        have b1e45 : (σ (M.op x y)) = (σ x) := by
          first
          | (have i₁ := b1e44
             have i₂ := b1e39 x
             grind)
          | exact superpose b1e39 b1e44
          | exact resolve b1e44 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39 b1e44
        have b1e46 : False := by grind
        exact b1e46
      · have b2e15 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op (M.op X1 X1) X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : y = (M.op (M.op y y) y) := by grind
        have b2e21 : (σ y) ≠ (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e37 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b2e15 X0 y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e15
          | (have j0 := b2e15 X0 y
             grind)
          | (have r₁ := b2e15 X0 y
             have r₂ := b2e20
             grind)
          | exact resolve b2e15 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e38 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
          intro X0
          first
          | (have j0 := b2e37 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37
        have b2e54 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e17 X0 (σ y)
             grind)
          | exact superpose b2e17 b2e21
          | (have j1 := b2e17 X0 (σ y)
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 X0 (σ y)
             grind)
          | exact resolve b2e21 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e55 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b2e54 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e54
        have b2e72 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 y
             have i₂ := b2e55 (σ X0)
             grind)
          | exact superpose b2e55 b2e18
          | (have j1 := b2e55 (σ X0)
             grind)
          | exact resolve b2e18 b2e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55
        have b2e78 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e72 X0
             have i₂ := b2e38 X0
             grind)
          | exact superpose b2e38 b2e72
          | (have j0 := b2e72 X0
             grind)
          | exact resolve b2e72 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38 b2e72
        have b2e357 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e78 x
             grind)
          | exact superpose b2e78 b2e19
          | (have j1 := b2e78 x
             grind)
          | (have r₁ := b2e19
             have r₂ := b2e78 x
             grind)
          | exact resolve b2e19 b2e78
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e78
        have b2e366 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b2e357
        have b2e369 : False := by grind
        exact b2e369
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (M.op (σ y) (σ y)) (σ y)) ((σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op (M.op X1 X1) X1) = X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op (M.op y y) y) := by grind
        have b3e21 : x = (M.op x y) := by grind
        have b3e22 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e19
          | exact resolve b3e19 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e38 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e15 X0 (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e15
          | (have j0 := b3e15 X0 (σ y)
             grind)
          | (have r₁ := b3e15 X0 (σ y)
             have r₂ := b3e22
             grind)
          | exact resolve b3e15 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e39 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b3e38 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38
        have b3e41 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 y
             have i₂ := b3e39 (σ X0)
             grind)
          | exact superpose b3e39 b3e18
          | exact resolve b3e18 b3e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39
        have b3e43 : x ≠ x ∨ y = (M.op (M.op y y) y) ∨ x = (k x y) := by
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
        have b3e44 : y = (M.op (M.op y y) y) ∨ x = (k x y) := by grind
        clear b3e43
        have b3e45 : x = (k x y) := by
          first
          | (have r₁ := b3e44
             have r₂ := b3e20
             grind)
          | exact resolve b3e44 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44
        have b3e112 : (σ x) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e41 x
             grind)
          | exact superpose b3e41 b3e23
          | exact resolve b3e23 b3e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e41
        have b3e118 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b3e112
             have i₂ := b3e45
             grind)
          | exact superpose b3e45 b3e112
          | exact resolve b3e112 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45 b3e112
        have b3e119 : False := by grind
        exact b3e119
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op x y) := by grind
          have b4e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e25 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e26 : (σ x) ≠ (σ x) := by
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
        · have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op (M.op X1 X1) X1) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op (M.op X1 X1) X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op (M.op y y) y) := by grind
          have b5e22 : x = (M.op x y) := by grind
          have b5e23 : (σ y) ≠ (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e48 : x ≠ x ∨ y = (M.op (M.op y y) y) ∨ x = (k x y) := by
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
          have b5e49 : y = (M.op (M.op y y) y) ∨ x = (k x y) := by grind
          clear b5e48
          have b5e50 : x = (k x y) := by
            first
            | (have r₁ := b5e49
               have r₂ := b5e21
               grind)
            | exact resolve b5e49 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49
          have b5e57 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e23
               have i₂ := b5e18 X0 (σ y)
               grind)
            | exact superpose b5e18 b5e23
            | (have j1 := b5e18 X0 (σ y)
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e18 X0 (σ y)
               grind)
            | exact resolve b5e23 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e60 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have j0 := b5e57 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e57
          have b5e95 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 y
               have i₂ := b5e60 (σ X0)
               grind)
            | exact superpose b5e60 b5e19
            | (have j1 := b5e60 (σ X0)
               grind)
            | exact resolve b5e19 b5e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e60
          have b5e358 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have j0 := b5e95 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e95
          have b5e770 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e358 x
               have i₂ := b5e50
               grind)
            | exact superpose b5e50 b5e358
            | (have j0 := b5e358 x
               grind)
            | exact resolve b5e358 b5e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50 b5e358
          have b5e773 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b5e770
          have b5e775 : False := by grind
          exact b5e775
    · rcases eq_or_ne (M.op (M.op (σ y) (σ y)) (σ y)) ((σ y)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op (M.op X1 X1) X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op (M.op y y) y) := by grind
        have b6e21 : x ≠ (M.op x y) := by grind
        have b6e22 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e37 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e15 X0 (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e15
          | (have j0 := b6e15 X0 (σ y)
             grind)
          | (have r₁ := b6e15 X0 (σ y)
             have r₂ := b6e22
             grind)
          | exact resolve b6e15 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e38 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b6e37 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e37
        have b6e40 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 y
             have i₂ := b6e38 (σ X0)
             grind)
          | exact superpose b6e38 b6e18
          | exact resolve b6e18 b6e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38
        have b6e57 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b6e20
             have i₂ := b6e17 X0 y
             grind)
          | exact superpose b6e17 b6e20
          | (have j1 := b6e17 X0 y
             grind)
          | (have r₁ := b6e20
             have r₂ := b6e17 X0 y
             grind)
          | exact resolve b6e20 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e58 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b6e57 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e57
        have b6e82 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e40 x
             grind)
          | exact superpose b6e40 b6e19
          | exact resolve b6e19 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40
        have b6e105 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e82
             have i₂ := b6e58 x
             grind)
          | exact superpose b6e58 b6e82
          | (have j1 := b6e58 x
             grind)
          | exact resolve b6e82 b6e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58 b6e82
        have b6e110 : x = (M.op x y) := by grind
        clear b6e105
        have b6e112 : False := by grind
        exact b6e112
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op (M.op X1 X1) X1) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op (M.op X1 X1) X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op (M.op y y) y) := by grind
          have b7e22 : x ≠ (M.op x y) := by grind
          have b7e23 : (σ y) ≠ (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e40 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e41 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e40
          have b7e42 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e41
               have r₂ := b7e23
               grind)
            | exact resolve b7e41 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41
          have b7e43 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e42
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e42
            | exact resolve b7e42 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e42
          have b7e46 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e43
               grind)
            | exact superpose b7e43 b7e14
            | exact resolve b7e14 b7e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e43
          have b7e47 : x = (k x y) := by
            first
            | (have i₁ := b7e46
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e46
            | exact resolve b7e46 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e56 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b7e21
               have i₂ := b7e18 X0 y
               grind)
            | exact superpose b7e18 b7e21
            | (have j1 := b7e18 X0 y
               grind)
            | (have r₁ := b7e21
               have r₂ := b7e18 X0 y
               grind)
            | exact resolve b7e21 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e57 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ (M.op X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b7e56 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e62 : x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e47
               have i₂ := b7e57 x
               grind)
            | exact superpose b7e57 b7e47
            | (have j1 := b7e57 x
               grind)
            | exact resolve b7e47 b7e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47 b7e57
          have b7e64 : x = (M.op x y) := by grind
          clear b7e62
          have b7e67 : False := by grind
          exact b7e67
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op (M.op X1 X1) X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op (M.op y y) y) := by grind
          have b8e22 : x ≠ (M.op x y) := by grind
          have b8e23 : (σ y) ≠ (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
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
          have b8e53 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 X0 (σ y)
               grind)
            | exact superpose b8e18 b8e23
            | (have j1 := b8e18 X0 (σ y)
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 X0 (σ y)
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e54 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b8e21
               have i₂ := b8e18 X0 y
               grind)
            | exact superpose b8e18 b8e21
            | (have j1 := b8e18 X0 y
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e18 X0 y
               grind)
            | exact resolve b8e21 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e55 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ (M.op X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b8e54 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e54
          have b8e56 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have j0 := b8e53 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e53
          have b8e72 : ∀ X0 : G, (k X0 (σ y)) = (σ (M.op (τ X0) y)) ∨ (τ X0) = (M.op (τ X0) y) := by
            intro X0
            first
            | (have i₁ := b8e25 X0 y
               have i₂ := b8e55 (τ X0)
               grind)
            | exact superpose b8e55 b8e25
            | (have j1 := b8e55 (τ X0)
               grind)
            | exact resolve b8e25 b8e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25 b8e55
          have b8e86 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 y
               have i₂ := b8e56 (σ X0)
               grind)
            | exact superpose b8e56 b8e19
            | (have j1 := b8e56 (σ X0)
               grind)
            | exact resolve b8e19 b8e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e56
          have b8e270 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (M.op X0 y)) ∨ (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b8e72 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e72
            | exact resolve b8e72 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72
          have b8e296 : ∀ X0 : G, (σ (k X0 y)) = (σ (M.op X0 y)) ∨ (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b8e270 X0
               have i₂ := b8e19 X0 y
               grind)
            | exact superpose b8e19 b8e270
            | (have j0 := b8e270 X0
               grind)
            | exact resolve b8e270 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e270
          have b8e333 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e86 x
               grind)
            | exact superpose b8e86 b8e20
            | (have j1 := b8e86 x
               grind)
            | exact resolve b8e20 b8e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e86
          have b8e341 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e333
               have r₂ := b8e24
               grind)
            | exact resolve b8e333 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e333
          have b8e347 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e341
               have i₂ := b8e296 x
               grind)
            | exact superpose b8e296 b8e341
            | (have j1 := b8e296 x
               grind)
            | (have r₁ := b8e341
               have r₂ := b8e296 x
               grind)
            | exact resolve b8e341 b8e296
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e296 b8e341
          have b8e348 : x = (M.op x y) := by grind
          clear b8e347
          have b8e353 : False := by grind
          exact b8e353
