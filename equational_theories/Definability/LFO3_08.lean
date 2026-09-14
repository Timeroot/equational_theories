import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,m(X,Y)) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pypxy_y_pyx_x_pyx_x_pyx_Equation1 :
    AutBox.GuardAut2 ((Lf 1) ⋆ ((Lf 0) ⋆ (Lf 1))) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ ((Lf 0) ⋆ (Lf 1))) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b (M.op a b) ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b (M.op a b)) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b (M.op a b) = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b (M.op a b)) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b (M.op a b) = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b (M.op a b)) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y (M.op x y)) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (M.op (σ x) (σ y))) ((σ y)) with h1a | h1a
    · have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 (M.op X0 X1)) = X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y (M.op x y)) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e22 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
      have b0e29 : y ≠ y ∨ (k x y) = (M.op y x) := by
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
      have b0e30 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
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
      have b0e31 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
      clear b0e30
      have b0e32 : (k x y) = (M.op y x) := by grind
      clear b0e29
      have b0e33 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
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
      have b0e34 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
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
      have b0e48 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
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
        | exact resolve b0e14 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e51 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e48 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48
      have b0e52 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e51 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e51
      have b0e58 : (σ x) ≠ (M.op (σ x) (σ (M.op y x))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b0e14 (σ y) (σ x)
           have i₂ := b0e34
           grind)
        | exact superpose b0e34 b0e14
        | (have j0 := b0e14 (σ y) (σ x)
           grind)
        | exact resolve b0e14 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e59 : (σ x) ≠ (M.op (σ x) (σ (M.op y x))) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
        first
        | (have i₁ := b0e58
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e58
        | exact resolve b0e58 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e58
      have b0e61 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e22 X0 X1
           have i₂ := b0e52 (τ X0) X1
           grind)
        | exact superpose b0e52 b0e22
        | (have j1 := b0e52 (τ X0) X1
           grind)
        | exact resolve b0e22 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22
      have b0e62 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X1 X0
           have i₂ := b0e52 (σ X0) (σ X1)
           grind)
        | exact superpose b0e52 b0e17
        | (have j1 := b0e52 (σ X0) (σ X1)
           grind)
        | exact resolve b0e17 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e52
      have b0e195 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e61 (σ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e61
        | exact resolve b0e61 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61
      have b0e219 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e195 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e195
        | (have j0 := b0e195 X0 X1
           grind)
        | exact resolve b0e195 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e195
      have b0e337 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e62 x y
           grind)
        | exact superpose b0e62 b0e18
        | (have j1 := b0e62 x y
           grind)
        | exact resolve b0e18 b0e62
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e344 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e62 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e62
      have b0e570 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e337
           have i₂ := b0e219 x y
           grind)
        | exact superpose b0e219 b0e337
        | (have j1 := b0e219 (σ x) (σ y)
           grind)
        | (have r₁ := b0e337
           have r₂ := b0e219 x y
           grind)
        | exact resolve b0e337 b0e219
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e337
      have b0e571 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
      clear b0e570
      have b0e578 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e571
           grind)
        | exact superpose b0e571 b0e18
        | exact resolve b0e18 b0e571
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e582 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e15 (σ y) (σ x)
           have i₂ := b0e571
           grind)
        | exact superpose b0e571 b0e15
        | (have j0 := b0e15 (σ y) (σ x)
           grind)
        | (have r₁ := b0e15 (σ y) (σ x)
           have r₂ := b0e571
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e571
           grind)
        | exact resolve b0e15 b0e571
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e584 : (σ x) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
      clear b0e582
      have b0e589 : (σ x) = (M.op (σ x) (σ (M.op y x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e584
           have i₂ := b0e34
           grind)
        | exact superpose b0e34 b0e584
        | exact resolve b0e584 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34 b0e584
      have b0e595 : (σ x) = (M.op (σ x) (σ (M.op y x))) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e589
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e589
        | exact resolve b0e589 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e589
      have b0e51671 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e59
           have i₂ := b0e595
           grind)
        | exact superpose b0e595 b0e59
        | (have r₁ := b0e59
           have r₂ := b0e595
           grind)
        | exact resolve b0e59 b0e595
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e59 b0e595
      have b0e51699 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by grind
      clear b0e51671
      have b0e100952 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e571
           have i₂ := b0e51699
           grind)
        | exact superpose b0e51699 b0e571
        | exact resolve b0e571 b0e51699
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e571 b0e51699
      have b0e101028 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by grind
      clear b0e100952
      have b0e101557 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e219 x y
           have i₂ := b0e101028
           grind)
        | exact superpose b0e101028 b0e219
        | (have j0 := b0e219 x y
           grind)
        | exact resolve b0e219 b0e101028
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e219 b0e101028
      have b0e101717 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
      clear b0e101557
      have b0e101777 : y = (M.op x y) := by
        first
        | (have r₁ := b0e101717
           have r₂ := b0e578
           grind)
        | exact resolve b0e101717 b0e578
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e578 b0e101717
      have b0e102286 : y ≠ y ∨ x = (M.op x (M.op y x)) ∨ y = (k y x) := by
        first
        | (have i₁ := b0e15 y x
           have i₂ := b0e101777
           grind)
        | exact superpose b0e101777 b0e15
        | (have j0 := b0e15 y x
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e101777
           grind)
        | exact resolve b0e15 b0e101777
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e102291 : x = (M.op x (M.op y x)) ∨ y = (k y x) := by grind
      clear b0e102286
      have b0e102666 : x ≠ x ∨ (M.op x y) = (k y x) ∨ y = (k y x) := by
        first
        | (have i₁ := b0e14 y x
           have i₂ := b0e102291
           grind)
        | exact superpose b0e102291 b0e14
        | (have j0 := b0e14 y x
           grind)
        | (have r₁ := b0e14 y x
           have r₂ := b0e102291
           grind)
        | exact resolve b0e14 b0e102291
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e102291
      have b0e102678 : (M.op x y) = (k y x) ∨ y = (k y x) := by grind
      clear b0e102666
      have b0e102680 : y = (k y x) ∨ y = (k y x) := by
        first
        | (have i₁ := b0e102678
           have i₂ := b0e101777
           grind)
        | exact superpose b0e101777 b0e102678
        | exact resolve b0e102678 b0e101777
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e102678
      have b0e102681 : y = (k y x) := by grind
      clear b0e102680
      have b0e103225 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e344 x y
           have i₂ := b0e102681
           grind)
        | exact superpose b0e102681 b0e344
        | (have j0 := b0e344 x y
           grind)
        | exact resolve b0e344 b0e102681
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e344 b0e102681
      have b0e103296 : (σ y) = (M.op (σ x) (σ y)) := by grind
      clear b0e103225
      have b0e104564 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e103296
           grind)
        | exact superpose b0e103296 b0e18
        | exact resolve b0e18 b0e103296
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e103296
      have b0e104587 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e104564
           have i₂ := b0e101777
           grind)
        | exact superpose b0e101777 b0e104564
        | exact resolve b0e104564 b0e101777
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e101777 b0e104564
      have b0e104588 : False := by grind
      exact b0e104588
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 (M.op X0 X1)) = X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op y (M.op x y)) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ y) (M.op (σ x) (σ y))) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b1e38 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b1e15 (σ y) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | (have j0 := b1e15 (σ y) (σ x)
             grind)
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e39 : y ≠ y ∨ (k x y) = (M.op y x) := by
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
        have b1e40 : (k x y) = (M.op y x) := by grind
        clear b1e39
        have b1e41 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b1e38
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e38
          | exact resolve b1e38 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38
        have b1e43 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e44 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e43
        have b1e45 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e44
             have r₂ := b1e21
             grind)
          | exact resolve b1e44 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e44
        have b1e46 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e45
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e45
          | exact resolve b1e45 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45
        have b1e47 : (σ x) = (σ (M.op y x)) := by
          first
          | (have i₁ := b1e46
             have i₂ := b1e40
             grind)
          | exact superpose b1e40 b1e46
          | exact resolve b1e46 b1e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40 b1e46
        have b1e50 : (M.op y x) = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 (M.op y x)
             have i₂ := b1e47
             grind)
          | exact superpose b1e47 b1e13
          | exact resolve b1e13 b1e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e51 : x = (M.op y x) := by
          first
          | (have i₁ := b1e50
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e50
          | exact resolve b1e50 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e50
        have b1e57 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
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
          | exact resolve b1e15 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e62 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b1e57 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57
        have b1e63 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b1e62 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e62
        have b1e68 : x ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
          first
          | (have i₁ := b1e15 y x
             have i₂ := b1e51
             grind)
          | exact superpose b1e51 b1e15
          | (have j0 := b1e15 y x
             grind)
          | exact resolve b1e15 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e71 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e24 X0 X1
             have i₂ := b1e63 (τ X0) X1
             grind)
          | exact superpose b1e63 b1e24
          | (have j1 := b1e63 (τ X0) X1
             grind)
          | exact resolve b1e24 b1e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24
        have b1e72 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X1 X0
             have i₂ := b1e63 (σ X0) (σ X1)
             grind)
          | exact superpose b1e63 b1e18
          | (have j1 := b1e63 (σ X0) (σ X1)
             grind)
          | exact resolve b1e18 b1e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e63
        have b1e227 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e71 (σ X0) X1
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e71
          | exact resolve b1e71 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e71
        have b1e251 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e227 X0 X1
             have i₂ := b1e18 X1 X0
             grind)
          | exact superpose b1e18 b1e227
          | (have j0 := b1e227 X0 X1
             grind)
          | exact resolve b1e227 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e227
        have b1e371 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e72 x y
             grind)
          | exact superpose b1e72 b1e19
          | (have j1 := b1e72 x y
             grind)
          | exact resolve b1e19 b1e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e372 : (σ x) ≠ (σ (k x x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e41
             have i₂ := b1e72 x x
             grind)
          | exact superpose b1e72 b1e41
          | (have j1 := b1e72 x y
             grind)
          | (have r₁ := b1e41
             have r₂ := b1e72 x x
             grind)
          | exact resolve b1e41 b1e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e378 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e72 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e72
        have b1e381 : (σ x) ≠ (σ (k x x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have r₁ := b1e372
             have r₂ := b1e41
             grind)
          | exact resolve b1e372 b1e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41 b1e372
        have b1e606 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e371
             have i₂ := b1e251 x y
             grind)
          | exact superpose b1e251 b1e371
          | (have j1 := b1e251 (σ x) (σ y)
             grind)
          | (have r₁ := b1e371
             have r₂ := b1e251 x y
             grind)
          | exact resolve b1e371 b1e251
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e371
        have b1e607 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
        clear b1e606
        have b1e611 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e607
             grind)
          | exact superpose b1e607 b1e19
          | exact resolve b1e19 b1e607
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e615 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e16 (σ y) (σ x)
             have i₂ := b1e607
             grind)
          | exact superpose b1e607 b1e16
          | (have j0 := b1e16 (σ y) (σ x)
             grind)
          | (have r₁ := b1e16 (σ y) (σ x)
             have r₂ := b1e607
             grind)
          | (have r₁ := b1e16 y x
             have r₂ := b1e607
             grind)
          | exact resolve b1e16 b1e607
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e607
        have b1e617 : (σ x) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
        clear b1e615
        have b1e620 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e617
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e617
          | exact resolve b1e617 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e617
        have b1e622 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e620
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e620
          | exact resolve b1e620 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e620
        have b1e12874 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e15 (σ x) (σ x)
             have i₂ := b1e622
             grind)
          | exact superpose b1e622 b1e15
          | exact resolve b1e15 b1e622
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e12879 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b1e12874
             have r₂ := b1e622
             grind)
          | exact resolve b1e12874 b1e622
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e622 b1e12874
        have b1e12880 : (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e12879
             have i₂ := b1e18 x x
             grind)
          | exact superpose b1e18 b1e12879
          | exact resolve b1e12879 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12879
        have b1e13165 : (τ (σ x)) = (k x x) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e13 (k x x)
             have i₂ := b1e12880
             grind)
          | exact superpose b1e12880 b1e13
          | exact resolve b1e13 b1e12880
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12880
        have b1e13226 : (σ y) = (σ (k y x)) ∨ x = (k x x) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e13165
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e13165
          | exact resolve b1e13165 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e13165
        have b1e13511 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (k x x) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e251 x y
             have i₂ := b1e13226
             grind)
          | exact superpose b1e13226 b1e251
          | (have j0 := b1e251 x y
             grind)
          | exact resolve b1e251 b1e13226
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e13226
        have b1e13554 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (k x x) := by grind
        clear b1e13511
        have b1e13578 : x = (k x x) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b1e13554
             have r₂ := b1e611
             grind)
          | exact resolve b1e13554 b1e611
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e611 b1e13554
        have b1e13868 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e381
             have i₂ := b1e13578
             grind)
          | exact superpose b1e13578 b1e381
          | exact resolve b1e381 b1e13578
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e13578
        have b1e13899 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x y) := by grind
        clear b1e13868
        have b1e15271 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e13899
             grind)
          | exact superpose b1e13899 b1e19
          | exact resolve b1e19 b1e13899
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e13899
        have b1e15309 : y = (M.op x y) := by
          first
          | (have j1 := b1e251 x y
             grind)
          | (have r₁ := b1e15271
             have r₂ := b1e251 x y
             grind)
          | exact resolve b1e15271 b1e251
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e251 b1e15271
        have b1e15639 : y ≠ y ∨ x = (M.op x (M.op y x)) ∨ y = (k y x) := by
          first
          | (have i₁ := b1e16 y x
             have i₂ := b1e15309
             grind)
          | exact superpose b1e15309 b1e16
          | (have j0 := b1e16 y x
             grind)
          | (have r₁ := b1e16 y x
             have r₂ := b1e15309
             grind)
          | exact resolve b1e16 b1e15309
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e15644 : x = (M.op x (M.op y x)) ∨ y = (k y x) := by grind
        clear b1e15639
        have b1e15648 : y = (k y x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e15644
             have i₂ := b1e51
             grind)
          | exact superpose b1e51 b1e15644
          | exact resolve b1e15644 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51 b1e15644
        have b1e17007 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e378 x y
             have i₂ := b1e15648
             grind)
          | exact superpose b1e15648 b1e378
          | (have j0 := b1e378 x y
             grind)
          | exact resolve b1e378 b1e15648
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e378 b1e15648
        have b1e17027 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
        clear b1e17007
        have b1e18916 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e17027
             grind)
          | exact superpose b1e17027 b1e19
          | exact resolve b1e19 b1e17027
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e17027
        have b1e18927 : (σ y) ≠ (σ y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e18916
             have i₂ := b1e15309
             grind)
          | exact superpose b1e15309 b1e18916
          | exact resolve b1e18916 b1e15309
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e18916
        have b1e18928 : x = (M.op x x) := by grind
        clear b1e18927
        have b1e19183 : x ≠ x ∨ (M.op x y) = (k y x) := by
          first
          | (have i₁ := b1e68
             have i₂ := b1e18928
             grind)
          | exact superpose b1e18928 b1e68
          | (have r₁ := b1e68
             have r₂ := b1e18928
             grind)
          | exact resolve b1e68 b1e18928
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e68
        have b1e19184 : x ≠ (M.op x x) ∨ x = (k x x) := by
          first
          | (have i₁ := b1e15 x x
             have i₂ := b1e18928
             grind)
          | exact superpose b1e18928 b1e15
          | exact resolve b1e15 b1e18928
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e19187 : (M.op x y) = (k y x) := by grind
        clear b1e19183
        have b1e19188 : x = (k x x) := by
          first
          | (have r₁ := b1e19184
             have r₂ := b1e18928
             grind)
          | exact resolve b1e19184 b1e18928
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e18928 b1e19184
        have b1e19189 : y = (k y x) := by
          first
          | (have i₁ := b1e19187
             have i₂ := b1e15309
             grind)
          | exact superpose b1e15309 b1e19187
          | exact resolve b1e19187 b1e15309
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e19187
        have b1e19439 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b1e381
             have i₂ := b1e19188
             grind)
          | exact superpose b1e19188 b1e381
          | exact resolve b1e381 b1e19188
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e381 b1e19188
        have b1e19484 : (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
        clear b1e19439
        have b1e19487 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e19484
             have i₂ := b1e19189
             grind)
          | exact superpose b1e19189 b1e19484
          | exact resolve b1e19484 b1e19189
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e19189 b1e19484
        have b1e21126 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e19487
             grind)
          | exact superpose b1e19487 b1e19
          | exact resolve b1e19 b1e19487
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e19487
        have b1e21137 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e21126
             have i₂ := b1e15309
             grind)
          | exact superpose b1e15309 b1e21126
          | exact resolve b1e21126 b1e15309
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e15309 b1e21126
        have b1e21138 : False := by grind
        exact b1e21138
      · have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 (M.op X0 X1)) = X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : y = (M.op y (M.op x y)) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (M.op (σ x) (σ y))) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b2e38 : y ≠ y ∨ (k x y) = (M.op y x) := by
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
        have b2e39 : (k x y) = (M.op y x) := by grind
        clear b2e38
        have b2e51 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
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
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e54 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e17 (σ x) (σ y)
             grind)
          | exact superpose b2e17 b2e21
          | (have j1 := b2e17 (σ x) (σ y)
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | exact resolve b2e21 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e55 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b2e54
        have b2e56 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e51 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51
        have b2e57 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e56 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e56
        have b2e58 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e55
             have r₂ := b2e22
             grind)
          | exact resolve b2e55 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55
        have b2e61 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e58
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e58
          | exact resolve b2e58 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e58
        have b2e62 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b2e61
             have i₂ := b2e39
             grind)
          | exact superpose b2e39 b2e61
          | exact resolve b2e61 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39 b2e61
        have b2e66 : (σ x) ≠ (M.op (σ x) (σ (M.op y x))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b2e15 (σ y) (σ x)
             have i₂ := b2e62
             grind)
          | exact superpose b2e62 b2e15
          | (have j0 := b2e15 (σ y) (σ x)
             grind)
          | exact resolve b2e15 b2e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e67 : (σ x) ≠ (M.op (σ x) (σ (M.op y x))) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b2e66
             have i₂ := b2e18 y x
             grind)
          | exact superpose b2e18 b2e66
          | exact resolve b2e66 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e66
        have b2e70 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e24 X0 X1
             have i₂ := b2e57 (τ X0) X1
             grind)
          | exact superpose b2e57 b2e24
          | (have j1 := b2e57 (τ X0) X1
             grind)
          | exact resolve b2e24 b2e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24
        have b2e72 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e57 (σ X0) (σ X1)
             grind)
          | exact superpose b2e57 b2e18
          | (have j1 := b2e57 (σ X0) (σ X1)
             grind)
          | exact resolve b2e18 b2e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57
        have b2e192 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e70 (σ X0) X1
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e70
          | exact resolve b2e70 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e70
        have b2e216 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e192 X0 X1
             have i₂ := b2e18 X1 X0
             grind)
          | exact superpose b2e18 b2e192
          | (have j0 := b2e192 X0 X1
             grind)
          | exact resolve b2e192 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e192
        have b2e334 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
        have b2e340 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e72 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e72
        have b2e576 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b2e334
             have i₂ := b2e216 x y
             grind)
          | exact superpose b2e216 b2e334
          | (have j1 := b2e216 (σ x) (σ y)
             grind)
          | (have r₁ := b2e334
             have r₂ := b2e216 x y
             grind)
          | exact resolve b2e334 b2e216
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e334
        have b2e577 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
        clear b2e576
        have b2e581 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e577
             grind)
          | exact superpose b2e577 b2e19
          | exact resolve b2e19 b2e577
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e585 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b2e16 (σ y) (σ x)
             have i₂ := b2e577
             grind)
          | exact superpose b2e577 b2e16
          | (have j0 := b2e16 (σ y) (σ x)
             grind)
          | (have r₁ := b2e16 (σ y) (σ x)
             have r₂ := b2e577
             grind)
          | (have r₁ := b2e16 y x
             have r₂ := b2e577
             grind)
          | exact resolve b2e16 b2e577
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e587 : (σ x) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
        clear b2e585
        have b2e590 : (σ x) = (M.op (σ x) (σ (M.op y x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b2e587
             have i₂ := b2e62
             grind)
          | exact superpose b2e62 b2e587
          | exact resolve b2e587 b2e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e62 b2e587
        have b2e592 : (σ x) = (M.op (σ x) (σ (M.op y x))) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b2e590
             have i₂ := b2e18 y x
             grind)
          | exact superpose b2e18 b2e590
          | exact resolve b2e590 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e590
        have b2e24359 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b2e67
             have i₂ := b2e592
             grind)
          | exact superpose b2e592 b2e67
          | (have r₁ := b2e67
             have r₂ := b2e592
             grind)
          | exact resolve b2e67 b2e592
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e67 b2e592
        have b2e24387 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by grind
        clear b2e24359
        have b2e65320 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b2e577
             have i₂ := b2e24387
             grind)
          | exact superpose b2e24387 b2e577
          | exact resolve b2e577 b2e24387
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e577 b2e24387
        have b2e65388 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by grind
        clear b2e65320
        have b2e65957 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b2e216 x y
             have i₂ := b2e65388
             grind)
          | exact superpose b2e65388 b2e216
          | (have j0 := b2e216 x y
             grind)
          | exact resolve b2e216 b2e65388
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e216 b2e65388
        have b2e66092 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
        clear b2e65957
        have b2e66152 : y = (M.op x y) := by
          first
          | (have r₁ := b2e66092
             have r₂ := b2e581
             grind)
          | exact resolve b2e66092 b2e581
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e581 b2e66092
        have b2e66287 : y ≠ y ∨ x = (M.op x (M.op y x)) ∨ y = (k y x) := by
          first
          | (have i₁ := b2e16 y x
             have i₂ := b2e66152
             grind)
          | exact superpose b2e66152 b2e16
          | (have j0 := b2e16 y x
             grind)
          | (have r₁ := b2e16 y x
             have r₂ := b2e66152
             grind)
          | exact resolve b2e16 b2e66152
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e66292 : x = (M.op x (M.op y x)) ∨ y = (k y x) := by grind
        clear b2e66287
        have b2e69684 : x ≠ x ∨ (M.op x y) = (k y x) ∨ y = (k y x) := by
          first
          | (have i₁ := b2e15 y x
             have i₂ := b2e66292
             grind)
          | exact superpose b2e66292 b2e15
          | (have j0 := b2e15 y x
             grind)
          | (have r₁ := b2e15 y x
             have r₂ := b2e66292
             grind)
          | exact resolve b2e15 b2e66292
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e66292
        have b2e69696 : (M.op x y) = (k y x) ∨ y = (k y x) := by grind
        clear b2e69684
        have b2e69698 : y = (k y x) ∨ y = (k y x) := by
          first
          | (have i₁ := b2e69696
             have i₂ := b2e66152
             grind)
          | exact superpose b2e66152 b2e69696
          | exact resolve b2e69696 b2e66152
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e69696
        have b2e69699 : y = (k y x) := by grind
        clear b2e69698
        have b2e70371 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e340 x y
             have i₂ := b2e69699
             grind)
          | exact superpose b2e69699 b2e340
          | (have j0 := b2e340 x y
             grind)
          | exact resolve b2e340 b2e69699
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e340 b2e69699
        have b2e70440 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b2e70371
        have b2e71674 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e70440
             grind)
          | exact superpose b2e70440 b2e19
          | exact resolve b2e19 b2e70440
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e70440
        have b2e71687 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e71674
             have i₂ := b2e66152
             grind)
          | exact superpose b2e66152 b2e71674
          | exact resolve b2e71674 b2e66152
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e66152 b2e71674
        have b2e71688 : False := by grind
        exact b2e71688
  · rcases eq_or_ne (M.op y x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (M.op (σ x) (σ y))) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 (M.op X0 X1)) = X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op y (M.op x y)) := by grind
        have b3e21 : x = (M.op y x) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e24 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e18 X1 (τ X0)
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e18
          | exact resolve b3e18 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e37 : x ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
          first
          | (have i₁ := b3e15 y x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e15
          | (have j0 := b3e15 y x
             grind)
          | exact resolve b3e15 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e39 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
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
        have b3e40 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
        clear b3e39
        have b3e41 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e40
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e40
          | exact resolve b3e40 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40
        have b3e42 : (σ x) ≠ (M.op (σ x) (σ (k x y))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b3e15 (σ y) (σ x)
             have i₂ := b3e41
             grind)
          | exact superpose b3e41 b3e15
          | (have j0 := b3e15 (σ y) (σ x)
             grind)
          | exact resolve b3e15 b3e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e43 : (σ x) ≠ (M.op (σ x) (σ (k x y))) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b3e42
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e42
          | exact resolve b3e42 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42
        have b3e44 : x ≠ x ∨ y = (M.op y (M.op x y)) ∨ x = (k x y) := by
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
        have b3e47 : y = (M.op y (M.op x y)) ∨ x = (k x y) := by grind
        clear b3e44
        have b3e48 : x = (k x y) := by
          first
          | (have r₁ := b3e47
             have r₂ := b3e20
             grind)
          | exact resolve b3e47 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47
        have b3e53 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
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
          | exact resolve b3e15 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e58 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b3e53 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53
        have b3e59 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b3e58 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e58
        have b3e85 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e24 X0 X1
             have i₂ := b3e59 (τ X0) X1
             grind)
          | exact superpose b3e59 b3e24
          | (have j1 := b3e59 (τ X0) X1
             grind)
          | exact resolve b3e24 b3e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e87 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e18 X1 X0
             have i₂ := b3e59 (σ X0) (σ X1)
             grind)
          | exact superpose b3e59 b3e18
          | (have j1 := b3e59 (σ X0) (σ X1)
             grind)
          | exact resolve b3e18 b3e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e202 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e85 (σ X0) X1
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e85
          | exact resolve b3e85 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e85
        have b3e226 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e202 X0 X1
             have i₂ := b3e18 X1 X0
             grind)
          | exact superpose b3e18 b3e202
          | (have j0 := b3e202 X0 X1
             grind)
          | exact resolve b3e202 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e202
        have b3e344 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e87 x y
             grind)
          | exact superpose b3e87 b3e19
          | (have j1 := b3e87 x y
             grind)
          | exact resolve b3e19 b3e87
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e350 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b3e87 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e395 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b3e43
             have i₂ := b3e48
             grind)
          | exact superpose b3e48 b3e43
          | exact resolve b3e43 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43
        have b3e593 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e344
             have i₂ := b3e226 x y
             grind)
          | exact superpose b3e226 b3e344
          | (have j1 := b3e226 (σ x) (σ y)
             grind)
          | (have r₁ := b3e344
             have r₂ := b3e226 x y
             grind)
          | exact resolve b3e344 b3e226
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e594 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
        clear b3e593
        have b3e600 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e594
             grind)
          | exact superpose b3e594 b3e22
          | exact resolve b3e22 b3e594
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e601 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e594
             grind)
          | exact superpose b3e594 b3e19
          | exact resolve b3e19 b3e594
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e605 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e16 (σ y) (σ x)
             have i₂ := b3e594
             grind)
          | exact superpose b3e594 b3e16
          | (have j0 := b3e16 (σ y) (σ x)
             grind)
          | (have r₁ := b3e16 (σ y) (σ x)
             have r₂ := b3e594
             grind)
          | (have r₁ := b3e16 y x
             have r₂ := b3e594
             grind)
          | exact resolve b3e16 b3e594
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e594
        have b3e607 : (σ x) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
        clear b3e605
        have b3e612 : (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e607
             have i₂ := b3e41
             grind)
          | exact superpose b3e41 b3e607
          | exact resolve b3e607 b3e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e41 b3e607
        have b3e617 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e612
             have i₂ := b3e48
             grind)
          | exact superpose b3e48 b3e612
          | exact resolve b3e612 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48 b3e612
        have b3e620 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e617
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e617
          | exact resolve b3e617 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e617
        have b3e641 : (σ x) ≠ (σ (k x x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e395
             have i₂ := b3e87 x x
             grind)
          | exact superpose b3e87 b3e395
          | (have j1 := b3e87 x y
             grind)
          | (have r₁ := b3e395
             have r₂ := b3e87 x x
             grind)
          | exact resolve b3e395 b3e87
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e87
        have b3e642 : (σ x) ≠ (σ (k x x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have r₁ := b3e641
             have r₂ := b3e395
             grind)
          | exact resolve b3e641 b3e395
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e395 b3e641
        have b3e645 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e15 (σ y) (σ y)
             have i₂ := b3e600
             grind)
          | exact superpose b3e600 b3e15
          | exact resolve b3e15 b3e600
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e647 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b3e645
             have r₂ := b3e600
             grind)
          | exact resolve b3e645 b3e600
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e600 b3e645
        have b3e648 : (σ y) = (σ (k y y)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e647
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e647
          | exact resolve b3e647 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e647
        have b3e715 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e13 (k y y)
             have i₂ := b3e648
             grind)
          | exact superpose b3e648 b3e13
          | exact resolve b3e13 b3e648
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e648
        have b3e754 : y = (k y y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e715
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e715
          | exact resolve b3e715 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e715
        have b3e825 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e59 y y
             have i₂ := b3e754
             grind)
          | exact superpose b3e754 b3e59
          | (have j0 := b3e59 y y
             grind)
          | exact resolve b3e59 b3e754
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e59 b3e754
        have b3e826 : y = (M.op x y) ∨ y = (M.op y y) := by grind
        clear b3e825
        have b3e908 : y ≠ y ∨ x = (M.op x (M.op y x)) ∨ y = (k y x) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e16 y x
             have i₂ := b3e826
             grind)
          | exact superpose b3e826 b3e16
          | (have j0 := b3e16 y x
             grind)
          | (have r₁ := b3e16 y x
             have r₂ := b3e826
             grind)
          | (have r₁ := b3e16 y y
             have r₂ := b3e826
             grind)
          | exact resolve b3e16 b3e826
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e910 : x = (M.op x (M.op y x)) ∨ y = (k y x) ∨ y = (M.op y y) := by grind
        clear b3e908
        have b3e913 : y = (k y x) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e910
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e910
          | exact resolve b3e910 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e910
        have b3e2002 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e350 x y
             have i₂ := b3e913
             grind)
          | exact superpose b3e913 b3e350
          | (have j0 := b3e350 x y
             grind)
          | exact resolve b3e350 b3e913
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e350 b3e913
        have b3e2006 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by grind
        clear b3e2002
        have b3e16920 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e2006
             grind)
          | exact superpose b3e2006 b3e19
          | exact resolve b3e19 b3e2006
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2006
        have b3e17158 : (σ y) ≠ (σ y) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e16920
             have i₂ := b3e826
             grind)
          | exact superpose b3e826 b3e16920
          | exact resolve b3e16920 b3e826
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e16920
        have b3e17159 : (σ y) ≠ (σ y) ∨ x = (M.op x x) ∨ y = (M.op y y) := by grind
        clear b3e17158
        have b3e17160 : x = (M.op x x) ∨ y = (M.op y y) := by grind
        clear b3e17159
        have b3e17369 : x ≠ x ∨ (M.op x y) = (k y x) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e37
             have i₂ := b3e17160
             grind)
          | exact superpose b3e17160 b3e37
          | (have r₁ := b3e37
             have r₂ := b3e17160
             grind)
          | exact resolve b3e37 b3e17160
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37 b3e17160
        have b3e17373 : (M.op x y) = (k y x) ∨ y = (M.op y y) := by grind
        clear b3e17369
        have b3e17851 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e344
             have i₂ := b3e17373
             grind)
          | exact superpose b3e17373 b3e344
          | exact resolve b3e344 b3e17373
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e344 b3e17373
        have b3e17863 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
        clear b3e17851
        have b3e19375 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e17863
             grind)
          | exact superpose b3e17863 b3e19
          | exact resolve b3e19 b3e17863
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e17863
        have b3e19751 : (σ y) ≠ (σ y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e19375
             have i₂ := b3e826
             grind)
          | exact superpose b3e826 b3e19375
          | exact resolve b3e19375 b3e826
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e826 b3e19375
        have b3e19752 : (σ y) ≠ (σ y) ∨ y = (M.op y y) := by grind
        clear b3e19751
        have b3e19753 : y = (M.op y y) := by grind
        clear b3e19752
        have b3e42397 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e15 (σ x) (σ x)
             have i₂ := b3e620
             grind)
          | exact superpose b3e620 b3e15
          | exact resolve b3e15 b3e620
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e42402 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b3e42397
             have r₂ := b3e620
             grind)
          | exact resolve b3e42397 b3e620
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e620 b3e42397
        have b3e42404 : (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e42402
             have i₂ := b3e18 x x
             grind)
          | exact superpose b3e18 b3e42402
          | exact resolve b3e42402 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42402
        have b3e43137 : (k x x) = (τ (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e42404
             grind)
          | exact superpose b3e42404 b3e13
          | exact resolve b3e13 b3e42404
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42404
        have b3e43284 : (σ y) = (σ (k y x)) ∨ x = (k x x) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e43137
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e43137
          | exact resolve b3e43137 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43137
        have b3e44037 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (k x x) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e226 x y
             have i₂ := b3e43284
             grind)
          | exact superpose b3e43284 b3e226
          | (have j0 := b3e226 x y
             grind)
          | exact resolve b3e226 b3e43284
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43284
        have b3e44133 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (k x x) := by grind
        clear b3e44037
        have b3e44193 : x = (k x x) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b3e44133
             have r₂ := b3e601
             grind)
          | exact resolve b3e44133 b3e601
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e601 b3e44133
        have b3e44937 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e642
             have i₂ := b3e44193
             grind)
          | exact superpose b3e44193 b3e642
          | exact resolve b3e642 b3e44193
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e642 b3e44193
        have b3e44982 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x y) := by grind
        clear b3e44937
        have b3e48006 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e44982
             grind)
          | exact superpose b3e44982 b3e19
          | exact resolve b3e19 b3e44982
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44982
        have b3e48065 : y = (M.op x y) := by
          first
          | (have j1 := b3e226 x y
             grind)
          | (have r₁ := b3e48006
             have r₂ := b3e226 x y
             grind)
          | exact resolve b3e48006 b3e226
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e226 b3e48006
        have b3e48306 : y ≠ (M.op y y) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e48065
             grind)
          | exact superpose b3e48065 b3e20
          | exact resolve b3e20 b3e48065
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48065
        have b3e48319 : False := by grind
        exact b3e48319
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 (M.op X0 X1)) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op y x) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b4e31 : x ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b4e16 y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e16
            | (have j0 := b4e16 y x
               grind)
            | exact resolve b4e16 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e32 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b4e16 (σ y) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | (have j0 := b4e16 (σ y) (σ x)
               grind)
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e33 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b4e32
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e32
            | exact resolve b4e32 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e52 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
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
            | exact resolve b4e16 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e59 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e52 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e52
          have b4e60 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e59 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e59
          have b4e85 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e26 X0 X1
               have i₂ := b4e60 (τ X0) X1
               grind)
            | exact superpose b4e60 b4e26
            | (have j1 := b4e60 (τ X0) X1
               grind)
            | exact resolve b4e26 b4e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26
          have b4e87 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 X0
               have i₂ := b4e60 (σ X0) (σ X1)
               grind)
            | exact superpose b4e60 b4e19
            | (have j1 := b4e60 (σ X0) (σ X1)
               grind)
            | exact resolve b4e19 b4e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e60
          have b4e228 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e85 (σ X0) X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e85
            | exact resolve b4e85 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e85
          have b4e254 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e228 X0 X1
               have i₂ := b4e19 X1 X0
               grind)
            | exact superpose b4e19 b4e228
            | (have j0 := b4e228 X0 X1
               grind)
            | exact resolve b4e228 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e228
          have b4e379 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e87 x y
               grind)
            | exact superpose b4e87 b4e20
            | (have j1 := b4e87 x y
               grind)
            | exact resolve b4e20 b4e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e380 : (σ x) ≠ (σ (k x x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e33
               have i₂ := b4e87 x x
               grind)
            | exact superpose b4e87 b4e33
            | (have j1 := b4e87 x y
               grind)
            | (have r₁ := b4e33
               have r₂ := b4e87 x x
               grind)
            | exact resolve b4e33 b4e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e386 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e87 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e87
          have b4e389 : (σ x) ≠ (σ (k x x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have r₁ := b4e380
               have r₂ := b4e33
               grind)
            | exact resolve b4e380 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33 b4e380
          have b4e565 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e379
               have i₂ := b4e254 x y
               grind)
            | exact superpose b4e254 b4e379
            | (have j1 := b4e254 (σ x) (σ y)
               grind)
            | (have r₁ := b4e379
               have r₂ := b4e254 x y
               grind)
            | exact resolve b4e379 b4e254
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e379
          have b4e566 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
          clear b4e565
          have b4e570 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e566
               grind)
            | exact superpose b4e566 b4e20
            | exact resolve b4e20 b4e566
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e574 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e17 (σ y) (σ x)
               have i₂ := b4e566
               grind)
            | exact superpose b4e566 b4e17
            | (have j0 := b4e17 (σ y) (σ x)
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e566
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e566
               grind)
            | exact resolve b4e17 b4e566
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e566
          have b4e576 : (σ x) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
          clear b4e574
          have b4e579 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e576
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e576
            | exact resolve b4e576 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e576
          have b4e582 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e579
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e579
            | exact resolve b4e579 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e579
          have b4e10974 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e16 (σ x) (σ x)
               have i₂ := b4e582
               grind)
            | exact superpose b4e582 b4e16
            | exact resolve b4e16 b4e582
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e10978 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b4e10974
               have r₂ := b4e582
               grind)
            | exact resolve b4e10974 b4e582
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e582 b4e10974
          have b4e10979 : (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e10978
               have i₂ := b4e19 x x
               grind)
            | exact superpose b4e19 b4e10978
            | exact resolve b4e10978 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10978
          have b4e11165 : (k x x) = (τ (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e14 (k x x)
               have i₂ := b4e10979
               grind)
            | exact superpose b4e10979 b4e14
            | exact resolve b4e14 b4e10979
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10979
          have b4e11222 : (σ y) = (σ (k y x)) ∨ x = (k x x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e11165
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e11165
            | exact resolve b4e11165 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e11165
          have b4e11614 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (k x x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e254 x y
               have i₂ := b4e11222
               grind)
            | exact superpose b4e11222 b4e254
            | (have j0 := b4e254 x y
               grind)
            | exact resolve b4e254 b4e11222
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e11222
          have b4e11654 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (k x x) := by grind
          clear b4e11614
          have b4e11678 : x = (k x x) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b4e11654
               have r₂ := b4e570
               grind)
            | exact resolve b4e11654 b4e570
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e570 b4e11654
          have b4e11897 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e389
               have i₂ := b4e11678
               grind)
            | exact superpose b4e11678 b4e389
            | exact resolve b4e389 b4e11678
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e11678
          have b4e11926 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x y) := by grind
          clear b4e11897
          have b4e13487 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e11926
               grind)
            | exact superpose b4e11926 b4e20
            | exact resolve b4e20 b4e11926
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e11926
          have b4e13519 : y = (M.op x y) := by
            first
            | (have j1 := b4e254 x y
               grind)
            | (have r₁ := b4e13487
               have r₂ := b4e254 x y
               grind)
            | exact resolve b4e13487 b4e254
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e254 b4e13487
          have b4e13805 : y ≠ y ∨ x = (M.op x (M.op y x)) ∨ y = (k y x) := by
            first
            | (have i₁ := b4e17 y x
               have i₂ := b4e13519
               grind)
            | exact superpose b4e13519 b4e17
            | (have j0 := b4e17 y x
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e13519
               grind)
            | exact resolve b4e17 b4e13519
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e13810 : x = (M.op x (M.op y x)) ∨ y = (k y x) := by grind
          clear b4e13805
          have b4e13812 : y = (k y x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e13810
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13810
            | exact resolve b4e13810 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13810
          have b4e14106 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e386 x y
               have i₂ := b4e13812
               grind)
            | exact superpose b4e13812 b4e386
            | (have j0 := b4e386 x y
               grind)
            | exact resolve b4e386 b4e13812
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e386 b4e13812
          have b4e14126 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
          clear b4e14106
          have b4e14809 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e14126
               grind)
            | exact superpose b4e14126 b4e20
            | exact resolve b4e20 b4e14126
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e14126
          have b4e14820 : (σ y) ≠ (σ y) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e14809
               have i₂ := b4e13519
               grind)
            | exact superpose b4e13519 b4e14809
            | exact resolve b4e14809 b4e13519
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e14809
          have b4e14821 : x = (M.op x x) := by grind
          clear b4e14820
          have b4e15090 : x ≠ x ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b4e31
               have i₂ := b4e14821
               grind)
            | exact superpose b4e14821 b4e31
            | (have r₁ := b4e31
               have r₂ := b4e14821
               grind)
            | exact resolve b4e31 b4e14821
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31
          have b4e15091 : x ≠ (M.op x x) ∨ x = (k x x) := by
            first
            | (have i₁ := b4e16 x x
               have i₂ := b4e14821
               grind)
            | exact superpose b4e14821 b4e16
            | exact resolve b4e16 b4e14821
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e15094 : (M.op x y) = (k y x) := by grind
          clear b4e15090
          have b4e15095 : x = (k x x) := by
            first
            | (have r₁ := b4e15091
               have r₂ := b4e14821
               grind)
            | exact resolve b4e15091 b4e14821
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e14821 b4e15091
          have b4e15096 : y = (k y x) := by
            first
            | (have i₁ := b4e15094
               have i₂ := b4e13519
               grind)
            | exact superpose b4e13519 b4e15094
            | exact resolve b4e15094 b4e13519
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e15094
          have b4e15304 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b4e389
               have i₂ := b4e15095
               grind)
            | exact superpose b4e15095 b4e389
            | exact resolve b4e389 b4e15095
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e389 b4e15095
          have b4e15339 : (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
          clear b4e15304
          have b4e15342 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e15339
               have i₂ := b4e15096
               grind)
            | exact superpose b4e15096 b4e15339
            | exact resolve b4e15339 b4e15096
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e15096 b4e15339
          have b4e16822 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e15342
               grind)
            | exact superpose b4e15342 b4e20
            | exact resolve b4e20 b4e15342
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e15342
          have b4e16833 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e16822
               have i₂ := b4e13519
               grind)
            | exact superpose b4e13519 b4e16822
            | exact resolve b4e16822 b4e13519
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13519 b4e16822
          have b4e16834 : False := by grind
          exact b4e16834
        · have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 (M.op X0 X1)) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op y (M.op x y)) := by grind
          have b5e22 : x = (M.op y x) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ y) (M.op (σ x) (σ y))) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e40 : x ≠ x ∨ y = (M.op y (M.op x y)) ∨ x = (k x y) := by
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
          have b5e41 : y = (M.op y (M.op x y)) ∨ x = (k x y) := by grind
          clear b5e40
          have b5e42 : x = (k x y) := by
            first
            | (have r₁ := b5e41
               have r₂ := b5e21
               grind)
            | exact resolve b5e41 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41
          have b5e48 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e18 (σ x) (σ y)
               grind)
            | exact superpose b5e18 b5e23
            | (have j1 := b5e18 (σ x) (σ y)
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | exact resolve b5e23 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e51 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b5e48
          have b5e54 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e51
               have r₂ := b5e24
               grind)
            | exact resolve b5e51 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51
          have b5e57 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e54
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e54
            | exact resolve b5e54 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e54
          have b5e58 : (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e57
               have i₂ := b5e42
               grind)
            | exact superpose b5e42 b5e57
            | exact resolve b5e57 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42 b5e57
          have b5e59 : False := by grind
          exact b5e59
    · rcases eq_or_ne (M.op (σ y) (M.op (σ x) (σ y))) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 (M.op X0 X1)) = X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op y (M.op x y)) := by grind
        have b6e21 : x ≠ (M.op y x) := by grind
        have b6e22 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
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
        have b6e38 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
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
        have b6e39 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
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
        have b6e41 : (σ x) ≠ (M.op (σ x) (σ (k x y))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ x)
             have i₂ := b6e40
             grind)
          | exact superpose b6e40 b6e15
          | (have j0 := b6e15 (σ y) (σ x)
             grind)
          | exact resolve b6e15 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e42 : (σ x) ≠ (M.op (σ x) (σ (k x y))) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b6e41
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e41
          | exact resolve b6e41 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41
        have b6e56 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
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
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e59 : y ≠ y ∨ x = (M.op y x) ∨ (M.op y x) = (k x y) := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e20
          | (have j1 := b6e17 x y
             grind)
          | (have r₁ := b6e20
             have r₂ := b6e17 x y
             grind)
          | exact resolve b6e20 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e60 : x = (M.op y x) ∨ (M.op y x) = (k x y) := by grind
        clear b6e59
        have b6e61 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e56 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e56
        have b6e62 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e61 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e61
        have b6e63 : (M.op y x) = (k x y) := by
          first
          | (have r₁ := b6e60
             have r₂ := b6e21
             grind)
          | exact resolve b6e60 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e60
        have b6e67 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e24 X0 X1
             have i₂ := b6e62 (τ X0) X1
             grind)
          | exact superpose b6e62 b6e24
          | (have j1 := b6e62 (τ X0) X1
             grind)
          | exact resolve b6e24 b6e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24
        have b6e69 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X1 X0
             have i₂ := b6e62 (σ X0) (σ X1)
             grind)
          | exact superpose b6e62 b6e18
          | (have j1 := b6e62 (σ X0) (σ X1)
             grind)
          | exact resolve b6e18 b6e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e217 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e67 (σ X0) X1
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e67
          | exact resolve b6e67 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e67
        have b6e243 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e217 X0 X1
             have i₂ := b6e18 X1 X0
             grind)
          | exact superpose b6e18 b6e217
          | (have j0 := b6e217 X0 X1
             grind)
          | exact resolve b6e217 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e217
        have b6e368 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e69 x y
             grind)
          | exact superpose b6e69 b6e19
          | (have j1 := b6e69 x y
             grind)
          | exact resolve b6e19 b6e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e374 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b6e69 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e69
        have b6e423 : (σ x) ≠ (M.op (σ x) (σ (M.op y x))) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b6e42
             have i₂ := b6e63
             grind)
          | exact superpose b6e63 b6e42
          | exact resolve b6e42 b6e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42
        have b6e568 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e368
             have i₂ := b6e243 x y
             grind)
          | exact superpose b6e243 b6e368
          | (have j1 := b6e243 (σ x) (σ y)
             grind)
          | (have r₁ := b6e368
             have r₂ := b6e243 x y
             grind)
          | exact resolve b6e368 b6e243
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e368
        have b6e569 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
        clear b6e568
        have b6e575 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e569
             grind)
          | exact superpose b6e569 b6e22
          | exact resolve b6e22 b6e569
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e576 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e569
             grind)
          | exact superpose b6e569 b6e19
          | exact resolve b6e19 b6e569
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e580 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e16 (σ y) (σ x)
             have i₂ := b6e569
             grind)
          | exact superpose b6e569 b6e16
          | (have j0 := b6e16 (σ y) (σ x)
             grind)
          | (have r₁ := b6e16 (σ y) (σ x)
             have r₂ := b6e569
             grind)
          | (have r₁ := b6e16 y x
             have r₂ := b6e569
             grind)
          | exact resolve b6e16 b6e569
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e582 : (σ x) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
        clear b6e580
        have b6e587 : (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e582
             have i₂ := b6e40
             grind)
          | exact superpose b6e40 b6e582
          | exact resolve b6e582 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40 b6e582
        have b6e592 : (σ x) = (M.op (σ x) (σ (M.op y x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e587
             have i₂ := b6e63
             grind)
          | exact superpose b6e63 b6e587
          | exact resolve b6e587 b6e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e63 b6e587
        have b6e595 : (σ x) = (M.op (σ x) (σ (M.op y x))) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e592
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e592
          | exact resolve b6e592 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e592
        have b6e680 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e15 (σ y) (σ y)
             have i₂ := b6e575
             grind)
          | exact superpose b6e575 b6e15
          | exact resolve b6e15 b6e575
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e682 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b6e680
             have r₂ := b6e575
             grind)
          | exact resolve b6e680 b6e575
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e575 b6e680
        have b6e683 : (σ y) = (σ (k y y)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e682
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e682
          | exact resolve b6e682 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e682
        have b6e754 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e13 (k y y)
             have i₂ := b6e683
             grind)
          | exact superpose b6e683 b6e13
          | exact resolve b6e13 b6e683
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e683
        have b6e793 : y = (k y y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e754
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e754
          | exact resolve b6e754 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e754
        have b6e872 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e62 y y
             have i₂ := b6e793
             grind)
          | exact superpose b6e793 b6e62
          | (have j0 := b6e62 y y
             grind)
          | exact resolve b6e62 b6e793
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e62 b6e793
        have b6e873 : y = (M.op x y) ∨ y = (M.op y y) := by grind
        clear b6e872
        have b6e959 : y ≠ y ∨ x = (M.op x (M.op y x)) ∨ y = (k y x) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e16 y x
             have i₂ := b6e873
             grind)
          | exact superpose b6e873 b6e16
          | (have j0 := b6e16 y x
             grind)
          | (have r₁ := b6e16 y x
             have r₂ := b6e873
             grind)
          | (have r₁ := b6e16 y y
             have r₂ := b6e873
             grind)
          | exact resolve b6e16 b6e873
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e961 : x = (M.op x (M.op y x)) ∨ y = (k y x) ∨ y = (M.op y y) := by grind
        clear b6e959
        have b6e5483 : x ≠ x ∨ (M.op x y) = (k y x) ∨ y = (k y x) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e15 y x
             have i₂ := b6e961
             grind)
          | exact superpose b6e961 b6e15
          | (have j0 := b6e15 y x
             grind)
          | (have r₁ := b6e15 y x
             have r₂ := b6e961
             grind)
          | exact resolve b6e15 b6e961
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e961
        have b6e5489 : (M.op x y) = (k y x) ∨ y = (k y x) ∨ y = (M.op y y) := by grind
        clear b6e5483
        have b6e6697 : y ≠ (M.op x y) ∨ y = (k y x) ∨ y = (M.op y y) := by grind
        clear b6e5489
        have b6e6699 : y = (k y x) ∨ y = (M.op y y) := by
          first
          | (have r₁ := b6e6697
             have r₂ := b6e873
             grind)
          | exact resolve b6e6697 b6e873
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e6697
        have b6e6904 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e374 x y
             have i₂ := b6e6699
             grind)
          | exact superpose b6e6699 b6e374
          | (have j0 := b6e374 x y
             grind)
          | exact resolve b6e374 b6e6699
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e374 b6e6699
        have b6e6908 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
        clear b6e6904
        have b6e7051 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e6908
             grind)
          | exact superpose b6e6908 b6e19
          | exact resolve b6e19 b6e6908
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e6908
        have b6e7268 : (σ y) ≠ (σ y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e7051
             have i₂ := b6e873
             grind)
          | exact superpose b6e873 b6e7051
          | exact resolve b6e7051 b6e873
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e873 b6e7051
        have b6e7269 : (σ y) ≠ (σ y) ∨ y = (M.op y y) := by grind
        clear b6e7268
        have b6e7270 : y = (M.op y y) := by grind
        clear b6e7269
        have b6e76980 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e423
             have i₂ := b6e595
             grind)
          | exact superpose b6e595 b6e423
          | (have r₁ := b6e423
             have r₂ := b6e595
             grind)
          | exact resolve b6e423 b6e595
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e423 b6e595
        have b6e77008 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by grind
        clear b6e76980
        have b6e138136 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e569
             have i₂ := b6e77008
             grind)
          | exact superpose b6e77008 b6e569
          | exact resolve b6e569 b6e77008
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e569 b6e77008
        have b6e138226 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by grind
        clear b6e138136
        have b6e139163 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e243 x y
             have i₂ := b6e138226
             grind)
          | exact superpose b6e138226 b6e243
          | (have j0 := b6e243 x y
             grind)
          | exact resolve b6e243 b6e138226
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e243 b6e138226
        have b6e139342 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
        clear b6e139163
        have b6e139402 : y = (M.op x y) := by
          first
          | (have r₁ := b6e139342
             have r₂ := b6e576
             grind)
          | exact resolve b6e139342 b6e576
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e576 b6e139342
        have b6e140256 : y ≠ (M.op y y) := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e139402
             grind)
          | exact superpose b6e139402 b6e20
          | exact resolve b6e20 b6e139402
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e139402
        have b6e140266 : False := by grind
        exact b6e140266
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 (M.op X0 X1)) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op y (M.op x y)) := by grind
          have b7e22 : x ≠ (M.op y x) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ y) (M.op (σ x) (σ y))) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e41 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e42 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e41
          have b7e43 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e42
               have r₂ := b7e23
               grind)
            | exact resolve b7e42 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e42
          have b7e44 : (σ x) = (σ (k x y)) := by
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
          have b7e47 : (k x y) = (τ (σ x)) := by
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
          have b7e48 : x = (k x y) := by
            first
            | (have i₁ := b7e47
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e47
            | exact resolve b7e47 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
          have b7e57 : y ≠ y ∨ x = (M.op y x) ∨ (M.op y x) = (k x y) := by
            first
            | (have i₁ := b7e21
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e21
            | (have j1 := b7e18 x y
               grind)
            | (have r₁ := b7e21
               have r₂ := b7e18 x y
               grind)
            | exact resolve b7e21 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e58 : x = (M.op y x) ∨ (M.op y x) = (k x y) := by grind
          clear b7e57
          have b7e62 : (M.op y x) = (k x y) := by
            first
            | (have r₁ := b7e58
               have r₂ := b7e22
               grind)
            | exact resolve b7e58 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58
          have b7e64 : x = (M.op y x) := by
            first
            | (have i₁ := b7e62
               have i₂ := b7e48
               grind)
            | exact superpose b7e48 b7e62
            | exact resolve b7e62 b7e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48 b7e62
          have b7e65 : False := by grind
          exact b7e65
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 (M.op X0 X1)) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op y (M.op x y)) := by grind
          have b8e22 : x ≠ (M.op y x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ y) (M.op (σ x) (σ y))) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
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
          have b8e48 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
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
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e51 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 (σ x) (σ y)
               grind)
            | exact superpose b8e18 b8e23
            | (have j1 := b8e18 (σ x) (σ y)
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e52 : y ≠ y ∨ x = (M.op y x) ∨ (M.op y x) = (k x y) := by
            first
            | (have i₁ := b8e21
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e21
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e18 x y
               grind)
            | exact resolve b8e21 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e53 : x = (M.op y x) ∨ (M.op y x) = (k x y) := by grind
          clear b8e52
          have b8e54 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b8e51
          have b8e55 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e48 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e48
          have b8e56 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e55 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55
          have b8e57 : (M.op y x) = (k x y) := by
            first
            | (have r₁ := b8e53
               have r₂ := b8e22
               grind)
            | exact resolve b8e53 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e53
          have b8e58 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e54
               have r₂ := b8e24
               grind)
            | exact resolve b8e54 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e54
          have b8e60 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e58
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e58
            | exact resolve b8e58 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e58
          have b8e61 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
            first
            | (have i₁ := b8e60
               have i₂ := b8e57
               grind)
            | exact superpose b8e57 b8e60
            | exact resolve b8e60 b8e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e57 b8e60
          have b8e65 : (σ x) ≠ (M.op (σ x) (σ (M.op y x))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b8e16 (σ y) (σ x)
               have i₂ := b8e61
               grind)
            | exact superpose b8e61 b8e16
            | (have j0 := b8e16 (σ y) (σ x)
               grind)
            | exact resolve b8e16 b8e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e66 : (σ x) ≠ (M.op (σ x) (σ (M.op y x))) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e65
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e65
            | exact resolve b8e65 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e65
          have b8e69 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X0 X1
               have i₂ := b8e56 (τ X0) X1
               grind)
            | exact superpose b8e56 b8e26
            | (have j1 := b8e56 (τ X0) X1
               grind)
            | exact resolve b8e26 b8e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26
          have b8e71 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e56 (σ X0) (σ X1)
               grind)
            | exact superpose b8e56 b8e19
            | (have j1 := b8e56 (σ X0) (σ X1)
               grind)
            | exact resolve b8e19 b8e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e56
          have b8e215 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
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
          have b8e241 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e215 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e215
            | (have j0 := b8e215 X0 X1
               grind)
            | exact resolve b8e215 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e215
          have b8e367 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
          have b8e373 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e71 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e71
          have b8e571 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e367
               have i₂ := b8e241 x y
               grind)
            | exact superpose b8e241 b8e367
            | (have j1 := b8e241 (σ x) (σ y)
               grind)
            | (have r₁ := b8e367
               have r₂ := b8e241 x y
               grind)
            | exact resolve b8e367 b8e241
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e367
          have b8e572 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
          clear b8e571
          have b8e576 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e572
               grind)
            | exact superpose b8e572 b8e20
            | exact resolve b8e20 b8e572
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e580 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e572
               grind)
            | exact superpose b8e572 b8e17
            | (have j0 := b8e17 (σ y) (σ x)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e572
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e572
               grind)
            | exact resolve b8e17 b8e572
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e582 : (σ x) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
          clear b8e580
          have b8e585 : (σ x) = (M.op (σ x) (σ (M.op y x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e582
               have i₂ := b8e61
               grind)
            | exact superpose b8e61 b8e582
            | exact resolve b8e582 b8e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61 b8e582
          have b8e588 : (σ x) = (M.op (σ x) (σ (M.op y x))) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e585
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e585
            | exact resolve b8e585 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e585
          have b8e22388 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e66
               have i₂ := b8e588
               grind)
            | exact superpose b8e588 b8e66
            | (have r₁ := b8e66
               have r₂ := b8e588
               grind)
            | exact resolve b8e66 b8e588
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66 b8e588
          have b8e22416 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by grind
          clear b8e22388
          have b8e60748 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e572
               have i₂ := b8e22416
               grind)
            | exact superpose b8e22416 b8e572
            | exact resolve b8e572 b8e22416
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e572 b8e22416
          have b8e60806 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by grind
          clear b8e60748
          have b8e61434 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e241 x y
               have i₂ := b8e60806
               grind)
            | exact superpose b8e60806 b8e241
            | (have j0 := b8e241 x y
               grind)
            | exact resolve b8e241 b8e60806
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e241 b8e60806
          have b8e61565 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
          clear b8e61434
          have b8e61625 : y = (M.op x y) := by
            first
            | (have r₁ := b8e61565
               have r₂ := b8e576
               grind)
            | exact resolve b8e61565 b8e576
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e576 b8e61565
          have b8e62247 : y ≠ y ∨ x = (M.op x (M.op y x)) ∨ y = (k y x) := by
            first
            | (have i₁ := b8e17 y x
               have i₂ := b8e61625
               grind)
            | exact superpose b8e61625 b8e17
            | (have j0 := b8e17 y x
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e61625
               grind)
            | exact resolve b8e17 b8e61625
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e62252 : x = (M.op x (M.op y x)) ∨ y = (k y x) := by grind
          clear b8e62247
          have b8e63242 : x ≠ x ∨ (M.op x y) = (k y x) ∨ y = (k y x) := by
            first
            | (have i₁ := b8e16 y x
               have i₂ := b8e62252
               grind)
            | exact superpose b8e62252 b8e16
            | (have j0 := b8e16 y x
               grind)
            | (have r₁ := b8e16 y x
               have r₂ := b8e62252
               grind)
            | exact resolve b8e16 b8e62252
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62252
          have b8e63253 : (M.op x y) = (k y x) ∨ y = (k y x) := by grind
          clear b8e63242
          have b8e63258 : y = (k y x) ∨ y = (k y x) := by
            first
            | (have i₁ := b8e63253
               have i₂ := b8e61625
               grind)
            | exact superpose b8e61625 b8e63253
            | exact resolve b8e63253 b8e61625
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e63253
          have b8e63259 : y = (k y x) := by grind
          clear b8e63258
          have b8e63782 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e373 x y
               have i₂ := b8e63259
               grind)
            | exact superpose b8e63259 b8e373
            | (have j0 := b8e373 x y
               grind)
            | exact resolve b8e373 b8e63259
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e373 b8e63259
          have b8e63850 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b8e63782
          have b8e64905 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e63850
               grind)
            | exact superpose b8e63850 b8e20
            | exact resolve b8e20 b8e63850
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e63850
          have b8e64918 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b8e64905
               have i₂ := b8e61625
               grind)
            | exact superpose b8e61625 b8e64905
            | exact resolve b8e64905 b8e61625
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61625 b8e64905
          have b8e64919 : False := by grind
          exact b8e64919

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,m(Y,X)) = m(Y,X) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pypyx_pyx_pxy_y_pxy_y_pxy_Equation1 :
    AutBox.GuardAut2 ((Lf 1) ⋆ ((Lf 1) ⋆ (Lf 0))) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ ((Lf 1) ⋆ (Lf 0))) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b (M.op b a) ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b (M.op b a)) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b (M.op b a) = M.op b a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b (M.op b a)) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b (M.op b a) = M.op b a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b (M.op b a)) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y (M.op y x)) (M.op y x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (M.op (σ y) (σ x))) (M.op (σ y) (σ x)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 (M.op X1 X0)) ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op y x) = (M.op y (M.op y x)) := by grind
      have b0e20 : (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ y) (σ x))) := by grind
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
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 (M.op X1 X0)) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (M.op X1 (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op y x) = (M.op y (M.op y x)) := by grind
        have b1e21 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (M.op (σ y) (σ x))) := by grind
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
        have b1e45 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e48 : (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e45
        have b1e49 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e48
             have r₂ := b1e21
             grind)
          | exact resolve b1e48 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e48
        have b1e50 : (σ y) = (σ (k x y)) := by
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
        have b1e51 : (σ (M.op x y)) = (σ y) := by
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
      · have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 (M.op X1 X0)) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op y x) = (M.op y (M.op y x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
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
        have b2e54 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
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
        have b2e58 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e54 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e54
        have b2e59 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e58 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e58
        have b2e87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e336 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (M.op (σ y) (σ x))) (M.op (σ y) (σ x)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 (M.op X1 X0)) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (M.op X1 (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : (M.op y x) ≠ (M.op y (M.op y x)) := by grind
        have b3e21 : y = (M.op x y) := by grind
        have b3e22 : (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ y) (σ x))) := by grind
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
        have b3e45 : y ≠ y ∨ (M.op y x) = (M.op y (M.op y x)) ∨ y = (k x y) := by
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
        have b3e48 : (M.op y x) = (M.op y (M.op y x)) ∨ y = (k x y) := by grind
        clear b3e45
        have b3e49 : y = (k x y) := by
          first
          | (have r₁ := b3e48
             have r₂ := b3e20
             grind)
          | exact resolve b3e48 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48
        have b3e61 : (σ y) ≠ (σ (k x y)) := by
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
        have b3e66 : (σ y) ≠ (σ y) := by
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
        · have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (M.op X1 (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op y x) ≠ (M.op y (M.op y x)) := by grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e23 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (M.op (σ y) (σ x))) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e42 : y ≠ y ∨ (M.op y x) = (M.op y (M.op y x)) ∨ y = (k x y) := by
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
          have b5e43 : (M.op y x) = (M.op y (M.op y x)) ∨ y = (k x y) := by grind
          clear b5e42
          have b5e44 : y = (k x y) := by
            first
            | (have r₁ := b5e43
               have r₂ := b5e21
               grind)
            | exact resolve b5e43 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43
          have b5e50 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e18 (σ x) (σ y)
               grind)
            | exact superpose b5e18 b5e23
            | (have j1 := b5e18 (σ x) (σ y)
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e18 (σ y) (M.op (σ y) (σ x))
               grind)
            | exact resolve b5e23 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e53 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b5e50
          have b5e57 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e53
               have r₂ := b5e24
               grind)
            | exact resolve b5e53 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53
          have b5e58 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e57
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e57
            | exact resolve b5e57 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e57
          have b5e59 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e58
               have i₂ := b5e44
               grind)
            | exact superpose b5e44 b5e58
            | exact resolve b5e58 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44 b5e58
          have b5e60 : False := by grind
          exact b5e60
    · rcases eq_or_ne (M.op (σ y) (M.op (σ y) (σ x))) (M.op (σ y) (σ x)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 (M.op X1 X0)) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : (M.op y x) ≠ (M.op y (M.op y x)) := by grind
        have b6e21 : y ≠ (M.op x y) := by grind
        have b6e22 : (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ y) (σ x))) := by grind
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
        have b6e54 : (M.op y x) ≠ (M.op y x) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e20
          | (have j1 := b6e17 x y
             grind)
          | (have r₁ := b6e20
             have r₂ := b6e17 x y
             grind)
          | (have r₁ := b6e20
             have r₂ := b6e17 y (M.op y x)
             grind)
          | exact resolve b6e20 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e55 : y = (M.op x y) ∨ (M.op x y) = (k x y) := by grind
        clear b6e54
        have b6e59 : (M.op x y) = (k x y) := by
          first
          | (have r₁ := b6e55
             have r₂ := b6e21
             grind)
          | exact resolve b6e55 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55
        have b6e60 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b6e42
             have i₂ := b6e59
             grind)
          | exact superpose b6e59 b6e42
          | exact resolve b6e42 b6e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42 b6e59
        have b6e61 : False := by grind
        exact b6e61
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (M.op X1 (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : (M.op y x) ≠ (M.op y (M.op y x)) := by grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (M.op (σ y) (σ x))) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e43 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e44 : (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e43
          have b7e45 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e44
               have r₂ := b7e23
               grind)
            | exact resolve b7e44 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e46 : (σ y) = (σ (k x y)) := by
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
          have b7e49 : (k x y) = (τ (σ y)) := by
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
          have b7e50 : y = (k x y) := by
            first
            | (have i₁ := b7e49
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e49
            | exact resolve b7e49 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e59 : (M.op y x) ≠ (M.op y x) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) := by
            first
            | (have i₁ := b7e21
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e21
            | (have j1 := b7e18 x y
               grind)
            | (have r₁ := b7e21
               have r₂ := b7e18 x y
               grind)
            | (have r₁ := b7e21
               have r₂ := b7e18 y (M.op y x)
               grind)
            | exact resolve b7e21 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e60 : y = (M.op x y) ∨ (M.op x y) = (k x y) := by grind
          clear b7e59
          have b7e65 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b7e60
               have r₂ := b7e22
               grind)
            | exact resolve b7e60 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60
          have b7e66 : y = (M.op x y) := by
            first
            | (have i₁ := b7e65
               have i₂ := b7e50
               grind)
            | exact superpose b7e50 b7e65
            | exact resolve b7e65 b7e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50 b7e65
          have b7e67 : False := by grind
          exact b7e67
        · have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : (M.op y x) ≠ (M.op y (M.op y x)) := by grind
          have b8e22 : y ≠ (M.op x y) := by grind
          have b8e23 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (M.op (σ y) (σ x))) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e51 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 (σ x) (σ y)
               grind)
            | exact superpose b8e18 b8e23
            | (have j1 := b8e18 (σ x) (σ y)
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ y) (M.op (σ y) (σ x))
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e52 : (M.op y x) ≠ (M.op y x) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) := by
            first
            | (have i₁ := b8e21
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e21
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e18 x y
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e18 y (M.op y x)
               grind)
            | exact resolve b8e21 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e53 : y = (M.op x y) ∨ (M.op x y) = (k x y) := by grind
          clear b8e52
          have b8e54 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b8e51
          have b8e58 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b8e53
               have r₂ := b8e22
               grind)
            | exact resolve b8e53 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e53
          have b8e59 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e54
               have r₂ := b8e24
               grind)
            | exact resolve b8e54 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e54
          have b8e60 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e59
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e59
            | exact resolve b8e59 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e59
          have b8e61 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e60
               have i₂ := b8e58
               grind)
            | exact superpose b8e58 b8e60
            | exact resolve b8e60 b8e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e58 b8e60
          have b8e62 : False := by grind
          exact b8e62

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,m(Y,X)) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pypyx_pyy_pyx_y_pyx_y_pyx_Equation1 :
    AutBox.GuardAut2 ((Lf 1) ⋆ ((Lf 1) ⋆ (Lf 0))) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ ((Lf 1) ⋆ (Lf 0))) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b (M.op b a) ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b (M.op b a)) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b (M.op b a) = M.op b b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b (M.op b a)) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b (M.op b a) = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b (M.op b a)) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y (M.op y x)) (M.op y y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (M.op (σ y) (σ x))) (M.op (σ y) (σ y)) with h1a | h1a
    · have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
      have b0e50 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
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
        | exact resolve b0e14 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e53 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e50 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e50
      have b0e54 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e53 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e53
      have b0e69 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X1 X0
           have i₂ := b0e54 (σ X0) (σ X1)
           grind)
        | exact superpose b0e54 b0e17
        | (have j1 := b0e54 (σ X0) (σ X1)
           grind)
        | exact resolve b0e17 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e70 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e21 X1 X0
           have i₂ := b0e54 X0 (τ X1)
           grind)
        | exact superpose b0e54 b0e21
        | (have j1 := b0e54 X0 (τ X1)
           grind)
        | exact resolve b0e21 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21 b0e54
      have b0e249 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e70 X0 (σ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e70
        | exact resolve b0e70 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e70
      have b0e274 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e249 X0 X1
           have i₂ := b0e17 X0 X1
           grind)
        | exact superpose b0e17 b0e249
        | (have j0 := b0e249 X0 X1
           grind)
        | exact resolve b0e249 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e249
      have b0e409 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e69 x y
           grind)
        | exact superpose b0e69 b0e18
        | (have j1 := b0e69 x y
           grind)
        | exact resolve b0e18 b0e69
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e420 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e69 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e69
      have b0e782 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e409
           have i₂ := b0e274 y x
           grind)
        | exact superpose b0e274 b0e409
        | (have j1 := b0e274 (σ y) (σ x)
           grind)
        | (have r₁ := b0e409
           have r₂ := b0e274 y x
           grind)
        | exact resolve b0e409 b0e274
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e409
      have b0e783 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
      clear b0e782
      have b0e786 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e783
           grind)
        | exact superpose b0e783 b0e18
        | exact resolve b0e18 b0e783
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e787 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e14 (σ y) (σ x)
           have i₂ := b0e783
           grind)
        | exact superpose b0e783 b0e14
        | exact resolve b0e14 b0e783
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e783
      have b0e788 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
      clear b0e787
      have b0e789 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e788
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e788
        | exact resolve b0e788 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e788
      have b0e885 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e274 y x
           have i₂ := b0e789
           grind)
        | exact superpose b0e789 b0e274
        | (have j0 := b0e274 y x
           grind)
        | exact resolve b0e274 b0e789
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e274 b0e789
      have b0e911 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
      clear b0e885
      have b0e932 : x = (M.op x y) := by
        first
        | (have r₁ := b0e911
           have r₂ := b0e786
           grind)
        | exact resolve b0e911 b0e786
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e786 b0e911
      have b0e1011 : (M.op x x) ≠ (M.op x x) ∨ x = (k y x) := by
        first
        | (have i₁ := b0e14 y x
           have i₂ := b0e932
           grind)
        | exact superpose b0e932 b0e14
        | exact resolve b0e14 b0e932
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1012 : x = (k y x) := by grind
      clear b0e1011
      have b0e1102 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e420 x y
           have i₂ := b0e1012
           grind)
        | exact superpose b0e1012 b0e420
        | (have j0 := b0e420 x y
           grind)
        | exact resolve b0e420 b0e1012
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e420 b0e1012
      have b0e1106 : (σ x) = (M.op (σ x) (σ y)) := by grind
      clear b0e1102
      have b0e1199 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e1106
           grind)
        | exact superpose b0e1106 b0e18
        | exact resolve b0e18 b0e1106
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1106
      have b0e1203 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e1199
           have i₂ := b0e932
           grind)
        | exact superpose b0e932 b0e1199
        | exact resolve b0e1199 b0e932
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e932 b0e1199
      have b0e1204 : False := by grind
      exact b0e1204
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e21 : (M.op (σ y) (M.op (σ y) (σ x))) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) := by
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
      · have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e23 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 (τ X0) X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e18
          | exact resolve b2e18 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e52 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
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
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e55 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e52 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52
        have b2e56 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e55 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55
        have b2e74 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e56 (σ X0) (σ X1)
             grind)
          | exact superpose b2e56 b2e18
          | (have j1 := b2e56 (σ X0) (σ X1)
             grind)
          | exact resolve b2e18 b2e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e76 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e23 X1 X0
             have i₂ := b2e56 X0 (τ X1)
             grind)
          | exact superpose b2e56 b2e23
          | (have j1 := b2e56 X0 (τ X1)
             grind)
          | exact resolve b2e23 b2e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23 b2e56
        have b2e207 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e76 X0 (σ X0)
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e76
          | exact resolve b2e76 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e76
        have b2e232 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e207 X0 X1
             have i₂ := b2e18 X0 X1
             grind)
          | exact superpose b2e18 b2e207
          | (have j0 := b2e207 X0 X1
             grind)
          | exact resolve b2e207 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e207
        have b2e358 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e74 x y
             grind)
          | exact superpose b2e74 b2e19
          | (have j1 := b2e74 x y
             grind)
          | exact resolve b2e19 b2e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e364 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e74 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e74
        have b2e543 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e358
             have i₂ := b2e232 y x
             grind)
          | exact superpose b2e232 b2e358
          | (have j1 := b2e232 (σ y) (σ x)
             grind)
          | (have r₁ := b2e358
             have r₂ := b2e232 y x
             grind)
          | exact resolve b2e358 b2e232
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e358
        have b2e544 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
        clear b2e543
        have b2e547 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e544
             grind)
          | exact superpose b2e544 b2e19
          | exact resolve b2e19 b2e544
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e548 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e15 (σ y) (σ x)
             have i₂ := b2e544
             grind)
          | exact superpose b2e544 b2e15
          | exact resolve b2e15 b2e544
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e544
        have b2e549 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
        clear b2e548
        have b2e550 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e549
             have i₂ := b2e18 y x
             grind)
          | exact superpose b2e18 b2e549
          | exact resolve b2e549 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e549
        have b2e684 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e232 y x
             have i₂ := b2e550
             grind)
          | exact superpose b2e550 b2e232
          | (have j0 := b2e232 y x
             grind)
          | exact resolve b2e232 b2e550
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e232 b2e550
        have b2e707 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
        clear b2e684
        have b2e728 : x = (M.op x y) := by
          first
          | (have r₁ := b2e707
             have r₂ := b2e547
             grind)
          | exact resolve b2e707 b2e547
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e547 b2e707
        have b2e808 : (M.op x x) ≠ (M.op x x) ∨ x = (k y x) := by
          first
          | (have i₁ := b2e15 y x
             have i₂ := b2e728
             grind)
          | exact superpose b2e728 b2e15
          | exact resolve b2e15 b2e728
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e809 : x = (k y x) := by grind
        clear b2e808
        have b2e893 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e364 x y
             have i₂ := b2e809
             grind)
          | exact superpose b2e809 b2e364
          | (have j0 := b2e364 x y
             grind)
          | exact resolve b2e364 b2e809
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e364 b2e809
        have b2e897 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b2e893
        have b2e987 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e897
             grind)
          | exact superpose b2e897 b2e19
          | exact resolve b2e19 b2e897
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e897
        have b2e991 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e987
             have i₂ := b2e728
             grind)
          | exact superpose b2e728 b2e987
          | exact resolve b2e987 b2e728
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e728 b2e987
        have b2e992 : False := by grind
        exact b2e992
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (M.op (σ y) (σ x))) (M.op (σ y) (σ y)) with h1a | h1a
      · have b3e20 : (M.op y (M.op y x)) ≠ (M.op y y) := by grind
        have b3e21 : y = (M.op y x) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : (M.op y y) ≠ (M.op y y) := by
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
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e23 : (M.op (σ y) (M.op (σ y) (σ x))) ≠ (M.op (σ y) (σ y)) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e25 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) := by
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
        · have b5e21 : (M.op y (M.op y x)) ≠ (M.op y y) := by grind
          have b5e22 : y = (M.op y x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : (M.op y y) ≠ (M.op y y) := by
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
    · rcases eq_or_ne (M.op (σ y) (M.op (σ y) (σ x))) (M.op (σ y) (σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
        have b6e59 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
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
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e62 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e59 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e59
        have b6e63 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e62 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e62
        have b6e81 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X1 X0
             have i₂ := b6e63 (σ X0) (σ X1)
             grind)
          | exact superpose b6e63 b6e18
          | (have j1 := b6e63 (σ X0) (σ X1)
             grind)
          | exact resolve b6e18 b6e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e83 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b6e23 X1 X0
             have i₂ := b6e63 X0 (τ X1)
             grind)
          | exact superpose b6e63 b6e23
          | (have j1 := b6e63 X0 (τ X1)
             grind)
          | exact resolve b6e23 b6e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23 b6e63
        have b6e245 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e83 X0 (σ X0)
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e83
          | exact resolve b6e83 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e83
        have b6e270 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e245 X0 X1
             have i₂ := b6e18 X0 X1
             grind)
          | exact superpose b6e18 b6e245
          | (have j0 := b6e245 X0 X1
             grind)
          | exact resolve b6e245 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e245
        have b6e401 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e81 x y
             grind)
          | exact superpose b6e81 b6e19
          | (have j1 := b6e81 x y
             grind)
          | exact resolve b6e19 b6e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e412 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b6e81 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e81
        have b6e846 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e401
             have i₂ := b6e270 y x
             grind)
          | exact superpose b6e270 b6e401
          | (have j1 := b6e270 (σ y) (σ x)
             grind)
          | (have r₁ := b6e401
             have r₂ := b6e270 y x
             grind)
          | exact resolve b6e401 b6e270
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e401
        have b6e847 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
        clear b6e846
        have b6e850 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e847
             grind)
          | exact superpose b6e847 b6e19
          | exact resolve b6e19 b6e847
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e851 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e15 (σ y) (σ x)
             have i₂ := b6e847
             grind)
          | exact superpose b6e847 b6e15
          | exact resolve b6e15 b6e847
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e847
        have b6e852 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
        clear b6e851
        have b6e853 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e852
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e852
          | exact resolve b6e852 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e852
        have b6e941 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e270 y x
             have i₂ := b6e853
             grind)
          | exact superpose b6e853 b6e270
          | (have j0 := b6e270 y x
             grind)
          | exact resolve b6e270 b6e853
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e270 b6e853
        have b6e967 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
        clear b6e941
        have b6e988 : x = (M.op x y) := by
          first
          | (have r₁ := b6e967
             have r₂ := b6e850
             grind)
          | exact resolve b6e967 b6e850
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e850 b6e967
        have b6e1067 : (M.op x x) ≠ (M.op x x) ∨ x = (k y x) := by
          first
          | (have i₁ := b6e15 y x
             have i₂ := b6e988
             grind)
          | exact superpose b6e988 b6e15
          | exact resolve b6e15 b6e988
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1068 : x = (k y x) := by grind
        clear b6e1067
        have b6e1159 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e412 x y
             have i₂ := b6e1068
             grind)
          | exact superpose b6e1068 b6e412
          | (have j0 := b6e412 x y
             grind)
          | exact resolve b6e412 b6e1068
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e412 b6e1068
        have b6e1163 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b6e1159
        have b6e1257 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e1163
             grind)
          | exact superpose b6e1163 b6e19
          | exact resolve b6e19 b6e1163
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1163
        have b6e1261 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b6e1257
             have i₂ := b6e988
             grind)
          | exact superpose b6e988 b6e1257
          | exact resolve b6e1257 b6e988
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e988 b6e1257
        have b6e1262 : False := by grind
        exact b6e1262
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e23 : (M.op (σ y) (M.op (σ y) (σ x))) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) := by
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
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b8e50 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
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
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e53 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e50 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e50
          have b8e54 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e53 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e53
          have b8e70 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e72 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
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
          have b8e173 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e72 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e72
            | exact resolve b8e72 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72
          have b8e196 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e173 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e173
            | (have j0 := b8e173 X0 X1
               grind)
            | exact resolve b8e173 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e173
          have b8e313 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e70 x y
               grind)
            | exact superpose b8e70 b8e20
            | (have j1 := b8e70 x y
               grind)
            | exact resolve b8e20 b8e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e319 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e70 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e70
          have b8e546 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e313
               have i₂ := b8e196 y x
               grind)
            | exact superpose b8e196 b8e313
            | (have j1 := b8e196 (σ y) (σ x)
               grind)
            | (have r₁ := b8e313
               have r₂ := b8e196 y x
               grind)
            | exact resolve b8e313 b8e196
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e313
          have b8e547 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
          clear b8e546
          have b8e550 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e547
               grind)
            | exact superpose b8e547 b8e20
            | exact resolve b8e20 b8e547
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e551 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e16 (σ y) (σ x)
               have i₂ := b8e547
               grind)
            | exact superpose b8e547 b8e16
            | exact resolve b8e16 b8e547
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e547
          have b8e552 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b8e551
          have b8e553 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e552
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e552
            | exact resolve b8e552 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e552
          have b8e689 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e196 y x
               have i₂ := b8e553
               grind)
            | exact superpose b8e553 b8e196
            | (have j0 := b8e196 y x
               grind)
            | exact resolve b8e196 b8e553
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e196 b8e553
          have b8e713 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
          clear b8e689
          have b8e734 : x = (M.op x y) := by
            first
            | (have r₁ := b8e713
               have r₂ := b8e550
               grind)
            | exact resolve b8e713 b8e550
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e550 b8e713
          have b8e815 : (M.op x x) ≠ (M.op x x) ∨ x = (k y x) := by
            first
            | (have i₁ := b8e16 y x
               have i₂ := b8e734
               grind)
            | exact superpose b8e734 b8e16
            | exact resolve b8e16 b8e734
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e816 : x = (k y x) := by grind
          clear b8e815
          have b8e901 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e319 x y
               have i₂ := b8e816
               grind)
            | exact superpose b8e816 b8e319
            | (have j0 := b8e319 x y
               grind)
            | exact resolve b8e319 b8e816
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e319 b8e816
          have b8e905 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b8e901
          have b8e996 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e905
               grind)
            | exact superpose b8e905 b8e20
            | exact resolve b8e20 b8e905
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e905
          have b8e1000 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b8e996
               have i₂ := b8e734
               grind)
            | exact superpose b8e734 b8e996
            | exact resolve b8e996 b8e734
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e734 b8e996
          have b8e1001 : False := by grind
          exact b8e1001

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,m(Y,X)) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pypyx_x_pxy_y_pxy_y_pxy_Equation1 :
    AutBox.GuardAut2 ((Lf 1) ⋆ ((Lf 1) ⋆ (Lf 0))) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ ((Lf 1) ⋆ (Lf 0))) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b (M.op b a) ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b (M.op b a)) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b (M.op b a) = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b (M.op b a)) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b (M.op b a) = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b (M.op b a)) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y (M.op y x)) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (M.op (σ y) (σ x))) ((σ x)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op y (M.op y x)) := by grind
      have b0e20 : (σ x) = (M.op (σ y) (M.op (σ y) (σ x))) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e29 : x ≠ x ∨ (M.op x y) = (k x y) := by
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
      have b0e30 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
      have b0e35 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
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
        | (have i₁ := b0e35
           have i₂ := b0e32
           grind)
        | exact superpose b0e32 b0e35
        | exact resolve b0e35 b0e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32 b0e35
      have b0e37 : False := by grind
      exact b0e37
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 (M.op X1 X0)) = X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : x = (M.op y (M.op y x)) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ y) (M.op (σ y) (σ x))) := by grind
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
        have b1e40 : x ≠ x ∨ (M.op x y) = (k x y) := by
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
        have b1e46 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e47 : (σ x) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e46
        have b1e48 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e47
             have r₂ := b1e21
             grind)
          | exact resolve b1e47 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e49 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e48
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e48
          | exact resolve b1e48 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e48
        have b1e50 : (σ (M.op x y)) = (σ y) := by
          first
          | (have i₁ := b1e49
             have i₂ := b1e41
             grind)
          | exact superpose b1e41 b1e49
          | exact resolve b1e49 b1e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41 b1e49
        have b1e51 : False := by grind
        exact b1e51
      · have b2e15 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : x = (M.op y (M.op y x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e38 : x ≠ x ∨ (M.op x y) = (k x y) := by
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
        have b2e51 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
        have b2e55 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e51 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51
        have b2e56 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e55 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55
        have b2e84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e56 (σ X0) (σ X1)
             grind)
          | exact superpose b2e56 b2e18
          | (have j1 := b2e56 (σ X0) (σ X1)
             grind)
          | exact resolve b2e18 b2e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e56
        have b2e321 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e84 x y
             grind)
          | exact superpose b2e84 b2e19
          | (have j1 := b2e84 x y
             grind)
          | exact resolve b2e19 b2e84
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e84
        have b2e332 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e321
             have r₂ := b2e22
             grind)
          | exact resolve b2e321 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e321
        have b2e336 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b2e332
             have i₂ := b2e39
             grind)
          | exact superpose b2e39 b2e332
          | exact resolve b2e332 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39 b2e332
        have b2e337 : False := by grind
        exact b2e337
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (M.op (σ y) (σ x))) ((σ x)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 (M.op X1 X0)) = X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : x ≠ (M.op y (M.op y x)) := by grind
        have b3e21 : y = (M.op x y) := by grind
        have b3e22 : (σ x) = (M.op (σ y) (M.op (σ y) (σ x))) := by grind
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
        have b3e40 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b3e43 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
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
        have b3e45 : y ≠ y ∨ x = (M.op y (M.op y x)) ∨ y = (k x y) := by
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
        have b3e47 : x = (M.op y (M.op y x)) ∨ y = (k x y) := by grind
        clear b3e45
        have b3e48 : y = (k x y) := by
          first
          | (have r₁ := b3e47
             have r₂ := b3e20
             grind)
          | exact resolve b3e47 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47
        have b3e58 : (σ y) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e43
             grind)
          | exact superpose b3e43 b3e23
          | exact resolve b3e23 b3e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e43
        have b3e63 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b3e58
             have i₂ := b3e48
             grind)
          | exact superpose b3e48 b3e58
          | exact resolve b3e58 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48 b3e58
        have b3e64 : False := by grind
        exact b3e64
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
        · have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 (M.op X1 X0)) = X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ (M.op y (M.op y x)) := by grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ y) (M.op (σ y) (σ x))) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e42 : y ≠ y ∨ x = (M.op y (M.op y x)) ∨ y = (k x y) := by
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
          have b5e43 : x = (M.op y (M.op y x)) ∨ y = (k x y) := by grind
          clear b5e42
          have b5e44 : y = (k x y) := by
            first
            | (have r₁ := b5e43
               have r₂ := b5e21
               grind)
            | exact resolve b5e43 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43
          have b5e49 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e18 (σ x) (σ y)
               grind)
            | exact superpose b5e18 b5e23
            | (have j1 := b5e18 (σ x) (σ y)
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | exact resolve b5e23 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e52 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b5e49
          have b5e56 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e52
               have r₂ := b5e24
               grind)
            | exact resolve b5e52 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52
          have b5e57 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e56
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e56
            | exact resolve b5e56 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e56
          have b5e58 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e57
               have i₂ := b5e44
               grind)
            | exact superpose b5e44 b5e57
            | exact resolve b5e57 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44 b5e57
          have b5e59 : False := by grind
          exact b5e59
    · rcases eq_or_ne (M.op (σ y) (M.op (σ y) (σ x))) ((σ x)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : x ≠ (M.op y (M.op y x)) := by grind
        have b6e21 : y ≠ (M.op x y) := by grind
        have b6e22 : (σ x) = (M.op (σ y) (M.op (σ y) (σ x))) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e38 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b6e41 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
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
             have i₂ := b6e41
             grind)
          | exact superpose b6e41 b6e19
          | exact resolve b6e19 b6e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41
        have b6e51 : x ≠ x ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e20
          | (have j1 := b6e17 x y
             grind)
          | (have r₁ := b6e20
             have r₂ := b6e17 x y
             grind)
          | exact resolve b6e20 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e52 : y = (M.op x y) ∨ (M.op x y) = (k x y) := by grind
        clear b6e51
        have b6e56 : (M.op x y) = (k x y) := by
          first
          | (have r₁ := b6e52
             have r₂ := b6e21
             grind)
          | exact resolve b6e52 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e52
        have b6e57 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b6e42
             have i₂ := b6e56
             grind)
          | exact superpose b6e56 b6e42
          | exact resolve b6e42 b6e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42 b6e56
        have b6e58 : False := by grind
        exact b6e58
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 (M.op X1 X0)) = X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ (M.op y (M.op y x)) := by grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ y) (M.op (σ y) (σ x))) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e43 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e44 : (σ x) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e43
          have b7e45 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e44
               have r₂ := b7e23
               grind)
            | exact resolve b7e44 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e46 : (σ y) = (σ (k x y)) := by
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
          have b7e49 : (k x y) = (τ (σ y)) := by
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
          have b7e50 : y = (k x y) := by
            first
            | (have i₁ := b7e49
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e49
            | exact resolve b7e49 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e58 : x ≠ x ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) := by
            first
            | (have i₁ := b7e21
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e21
            | (have j1 := b7e18 x y
               grind)
            | (have r₁ := b7e21
               have r₂ := b7e18 x y
               grind)
            | exact resolve b7e21 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e59 : y = (M.op x y) ∨ (M.op x y) = (k x y) := by grind
          clear b7e58
          have b7e64 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b7e59
               have r₂ := b7e22
               grind)
            | exact resolve b7e59 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e59
          have b7e65 : y = (M.op x y) := by
            first
            | (have i₁ := b7e64
               have i₂ := b7e50
               grind)
            | exact superpose b7e50 b7e64
            | exact resolve b7e64 b7e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50 b7e64
          have b7e66 : False := by grind
          exact b7e66
        · have b8e18 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op y (M.op y x)) := by grind
          have b8e22 : y ≠ (M.op x y) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ y) (M.op (σ y) (σ x))) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e50 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 (σ x) (σ y)
               grind)
            | exact superpose b8e18 b8e23
            | (have j1 := b8e18 (σ x) (σ y)
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e51 : x ≠ x ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) := by
            first
            | (have i₁ := b8e21
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e21
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e18 x y
               grind)
            | exact resolve b8e21 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e52 : y = (M.op x y) ∨ (M.op x y) = (k x y) := by grind
          clear b8e51
          have b8e53 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b8e50
          have b8e57 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b8e52
               have r₂ := b8e22
               grind)
            | exact resolve b8e52 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e52
          have b8e58 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e53
               have r₂ := b8e24
               grind)
            | exact resolve b8e53 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e53
          have b8e59 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e58
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e58
            | exact resolve b8e58 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e58
          have b8e60 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e59
               have i₂ := b8e57
               grind)
            | exact superpose b8e57 b8e59
            | exact resolve b8e59 b8e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e57 b8e59
          have b8e61 : False := by grind
          exact b8e61

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,m(Y,X)) = X then m(Y,X) else if m(Y,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pypyx_x_pyx_x_pyx_pxy_pyx_Equation1 :
    AutBox.GuardAut2 ((Lf 1) ⋆ ((Lf 1) ⋆ (Lf 0))) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ ((Lf 1) ⋆ (Lf 0))) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b (M.op b a) ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b (M.op b a)) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b (M.op b a) = a ∨ M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b (M.op b a)) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b (M.op b a) = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b (M.op b a)) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y (M.op y x)) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (M.op (σ y) (σ x))) ((σ x)) with h1a | h1a
    · have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e22 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
      have b0e37 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
      have b0e40 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e37 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e41 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e40 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40
      have b0e87 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e22 X0 X1
           have i₂ := b0e41 X1 (τ X0)
           grind)
        | exact superpose b0e41 b0e22
        | (have j1 := b0e41 X1 (τ X0)
           grind)
        | exact resolve b0e22 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22
      have b0e89 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X1 X0
           have i₂ := b0e41 (σ X1) (σ X0)
           grind)
        | exact superpose b0e41 b0e17
        | (have j1 := b0e41 (σ X1) (σ X0)
           grind)
        | exact resolve b0e17 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41
      have b0e217 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e87 (σ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e87
        | exact resolve b0e87 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e87
      have b0e242 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e217 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e217
        | (have j0 := b0e217 X0 X1
           grind)
        | exact resolve b0e217 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e217
      have b0e367 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
      have b0e376 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e89 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e89
      have b0e643 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e367
           have i₂ := b0e242 x y
           grind)
        | exact superpose b0e242 b0e367
        | (have j1 := b0e242 (σ x) (σ y)
           grind)
        | (have r₁ := b0e367
           have r₂ := b0e242 x y
           grind)
        | exact resolve b0e367 b0e242
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e367
      have b0e644 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
      clear b0e643
      have b0e647 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e644
           grind)
        | exact superpose b0e644 b0e18
        | exact resolve b0e18 b0e644
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e649 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e14 (σ y) (σ x)
           have i₂ := b0e644
           grind)
        | exact superpose b0e644 b0e14
        | exact resolve b0e14 b0e644
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e651 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
        first
        | (have r₁ := b0e649
           have r₂ := b0e644
           grind)
        | exact resolve b0e649 b0e644
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e644 b0e649
      have b0e653 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e651
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e651
        | exact resolve b0e651 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e651
      have b0e789 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e242 x y
           have i₂ := b0e653
           grind)
        | exact superpose b0e653 b0e242
        | (have j0 := b0e242 x y
           grind)
        | exact resolve b0e242 b0e653
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e242 b0e653
      have b0e813 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
      clear b0e789
      have b0e834 : y = (M.op x y) := by
        first
        | (have r₁ := b0e813
           have r₂ := b0e647
           grind)
        | exact resolve b0e813 b0e647
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e647 b0e813
      have b0e915 : y ≠ (M.op x y) ∨ y = (k y x) := by
        first
        | (have i₁ := b0e14 y x
           have i₂ := b0e834
           grind)
        | exact superpose b0e834 b0e14
        | exact resolve b0e14 b0e834
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e917 : y = (k y x) := by
        first
        | (have r₁ := b0e915
           have r₂ := b0e834
           grind)
        | exact resolve b0e915 b0e834
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e915
      have b0e1002 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e376 x y
           have i₂ := b0e917
           grind)
        | exact superpose b0e917 b0e376
        | (have j0 := b0e376 x y
           grind)
        | exact resolve b0e376 b0e917
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e376 b0e917
      have b0e1006 : (σ y) = (M.op (σ x) (σ y)) := by grind
      clear b0e1002
      have b0e1099 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e1006
           grind)
        | exact superpose b0e1006 b0e18
        | exact resolve b0e18 b0e1006
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1006
      have b0e1104 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e1099
           have i₂ := b0e834
           grind)
        | exact superpose b0e834 b0e1099
        | exact resolve b0e1099 b0e834
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e834 b0e1099
      have b0e1105 : False := by grind
      exact b0e1105
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
      · have b1e21 : (σ x) ≠ (M.op (σ y) (M.op (σ y) (σ x))) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by
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
      · have b2e15 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op y (M.op y x)) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ y) (M.op (σ y) (σ x))) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e37 : (M.op y x) ≠ (M.op y x) ∨ x = (k (M.op y x) y) := by
          first
          | (have i₁ := b2e15 (M.op y x) y
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
        have b2e38 : x ≠ x ∨ (M.op y x) = (k x y) := by
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
        have b2e40 : x = (k (M.op y x) y) := by grind
        clear b2e37
        have b2e42 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
        have b2e45 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e42 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e42
        have b2e46 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b2e45 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e45
        have b2e60 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e46 (σ X1) (σ X0)
             grind)
          | exact superpose b2e46 b2e18
          | (have j1 := b2e46 (σ X1) (σ X0)
             grind)
          | exact resolve b2e18 b2e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e46
        have b2e324 : (σ x) ≠ (M.op (σ y) (σ (k x y))) ∨ (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e60 y x
             grind)
          | exact superpose b2e60 b2e21
          | (have j1 := b2e60 y x
             grind)
          | exact resolve b2e21 b2e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e332 : (σ x) ≠ (M.op (σ y) (σ (k x y))) := by
          first
          | (have r₁ := b2e324
             have r₂ := b2e22
             grind)
          | exact resolve b2e324 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e324
        have b2e335 : (σ x) ≠ (M.op (σ y) (σ (M.op y x))) := by
          first
          | (have i₁ := b2e332
             have i₂ := b2e39
             grind)
          | exact superpose b2e39 b2e332
          | exact resolve b2e332 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39 b2e332
        have b2e336 : (σ x) ≠ (σ (k (M.op y x) y)) ∨ (σ (M.op y x)) = (M.op (σ y) (σ (M.op y x))) := by
          first
          | (have i₁ := b2e335
             have i₂ := b2e60 y (M.op y x)
             grind)
          | exact superpose b2e60 b2e335
          | (have j1 := b2e60 y (M.op y x)
             grind)
          | exact resolve b2e335 b2e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e60
        have b2e337 : (σ x) ≠ (σ x) ∨ (σ (M.op y x)) = (M.op (σ y) (σ (M.op y x))) := by
          first
          | (have i₁ := b2e336
             have i₂ := b2e40
             grind)
          | exact superpose b2e40 b2e336
          | exact resolve b2e336 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e336
        have b2e338 : (σ (M.op y x)) = (M.op (σ y) (σ (M.op y x))) := by grind
        clear b2e337
        have b2e379 : (σ x) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b2e335
             have i₂ := b2e338
             grind)
          | exact superpose b2e338 b2e335
          | exact resolve b2e335 b2e338
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e335
        have b2e381 : (σ (M.op y x)) ≠ (M.op (σ y) (σ (M.op y x))) ∨ (σ (M.op y x)) = (k (σ (M.op y x)) (σ y)) := by
          first
          | (have i₁ := b2e15 (σ (M.op y x)) (σ y)
             have i₂ := b2e338
             grind)
          | exact superpose b2e338 b2e15
          | exact resolve b2e15 b2e338
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e383 : (σ (M.op y x)) = (k (σ (M.op y x)) (σ y)) := by
          first
          | (have r₁ := b2e381
             have r₂ := b2e338
             grind)
          | exact resolve b2e381 b2e338
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e338 b2e381
        have b2e384 : (σ (k (M.op y x) y)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b2e383
             have i₂ := b2e18 (M.op y x) y
             grind)
          | exact superpose b2e18 b2e383
          | exact resolve b2e383 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e383
        have b2e385 : (σ x) = (σ (M.op y x)) := by
          first
          | (have i₁ := b2e384
             have i₂ := b2e40
             grind)
          | exact superpose b2e40 b2e384
          | exact resolve b2e384 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40 b2e384
        have b2e386 : False := by grind
        exact b2e386
  · rcases eq_or_ne (M.op y x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (M.op (σ y) (σ x))) ((σ x)) with h1a | h1a
      · have b3e20 : x ≠ (M.op y (M.op y x)) := by grind
        have b3e21 : x = (M.op y x) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : x ≠ (M.op y x) := by
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
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b4e23 : (σ x) ≠ (M.op (σ y) (M.op (σ y) (σ x))) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e25 : (σ x) ≠ (M.op (σ y) (σ x)) := by
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
        · have b5e21 : x ≠ (M.op y (M.op y x)) := by grind
          have b5e22 : x = (M.op y x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : x ≠ (M.op y x) := by
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
    · rcases eq_or_ne (M.op (σ y) (M.op (σ y) (σ x))) ((σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op y (M.op y x)) := by grind
        have b6e21 : x ≠ (M.op y x) := by grind
        have b6e22 : (σ x) = (M.op (σ y) (M.op (σ y) (σ x))) := by grind
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
        have b6e37 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (σ x) = (k (M.op (σ y) (σ x)) (σ y)) := by
          first
          | (have i₁ := b6e15 (M.op (σ y) (σ x)) (σ y)
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
        have b6e38 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
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
        have b6e40 : (σ x) = (k (M.op (σ y) (σ x)) (σ y)) := by grind
        clear b6e37
        have b6e41 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
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
        have b6e55 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
        have b6e58 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e55 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55
        have b6e59 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e58 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58
        have b6e74 : (k (τ (M.op (σ y) (σ x))) y) = (τ (σ x)) := by
          first
          | (have i₁ := b6e28 (M.op (σ y) (σ x)) y
             have i₂ := b6e40
             grind)
          | exact superpose b6e40 b6e28
          | exact resolve b6e28 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28 b6e40
        have b6e75 : x = (k (τ (M.op (σ y) (σ x))) y) := by
          first
          | (have i₁ := b6e74
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e74
          | exact resolve b6e74 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e74
        have b6e77 : x = (k (τ (σ (k x y))) y) := by
          first
          | (have i₁ := b6e75
             have i₂ := b6e41
             grind)
          | exact superpose b6e41 b6e75
          | exact resolve b6e75 b6e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41 b6e75
        have b6e78 : x = (k (k x y) y) := by
          first
          | (have i₁ := b6e77
             have i₂ := b6e13 (k x y)
             grind)
          | exact superpose b6e13 b6e77
          | exact resolve b6e77 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e77
        have b6e89 : x = (k (M.op y x) y) ∨ x = (M.op y x) := by
          first
          | (have i₁ := b6e78
             have i₂ := b6e59 x y
             grind)
          | exact superpose b6e59 b6e78
          | (have j1 := b6e59 x y
             grind)
          | exact resolve b6e78 b6e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e78
        have b6e90 : x = (k (M.op y x) y) := by
          first
          | (have r₁ := b6e89
             have r₂ := b6e21
             grind)
          | exact resolve b6e89 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e89
        have b6e92 : x = (M.op y (M.op y x)) ∨ (M.op y x) = (M.op y (M.op y x)) := by
          first
          | (have i₁ := b6e59 (M.op y x) y
             have i₂ := b6e90
             grind)
          | exact superpose b6e90 b6e59
          | (have j0 := b6e59 (M.op y x) y
             grind)
          | exact resolve b6e59 b6e90
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e59
        have b6e93 : (M.op y x) = (M.op y (M.op y x)) := by
          first
          | (have r₁ := b6e92
             have r₂ := b6e20
             grind)
          | exact resolve b6e92 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e92
        have b6e129 : (M.op y x) ≠ (M.op y (M.op y x)) ∨ (M.op y x) = (k (M.op y x) y) := by
          first
          | (have i₁ := b6e15 (M.op y x) y
             have i₂ := b6e93
             grind)
          | exact superpose b6e93 b6e15
          | exact resolve b6e15 b6e93
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e133 : (M.op y x) = (k (M.op y x) y) := by
          first
          | (have r₁ := b6e129
             have r₂ := b6e93
             grind)
          | exact resolve b6e129 b6e93
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e93 b6e129
        have b6e134 : x = (M.op y x) := by
          first
          | (have i₁ := b6e133
             have i₂ := b6e90
             grind)
          | exact superpose b6e90 b6e133
          | exact resolve b6e133 b6e90
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e90 b6e133
        have b6e135 : False := by grind
        exact b6e135
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b7e23 : (σ x) ≠ (M.op (σ y) (M.op (σ y) (σ x))) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (σ x) ≠ (M.op (σ y) (σ x)) := by
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
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
          have b8e49 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b8e52 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e49 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e49
          have b8e53 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e52 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e52
          have b8e69 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e53 (σ X1) (σ X0)
               grind)
            | exact superpose b8e53 b8e19
            | (have j1 := b8e53 (σ X1) (σ X0)
               grind)
            | exact resolve b8e19 b8e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e72 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X0 X1
               have i₂ := b8e53 X1 (τ X0)
               grind)
            | exact superpose b8e53 b8e26
            | (have j1 := b8e53 X1 (τ X0)
               grind)
            | exact resolve b8e26 b8e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e53
          have b8e208 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e72 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e72
            | exact resolve b8e72 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72
          have b8e235 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
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
          have b8e361 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e69 x y
               grind)
            | exact superpose b8e69 b8e20
            | (have j1 := b8e69 x y
               grind)
            | exact resolve b8e20 b8e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e366 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e69 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e69
          have b8e549 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e361
               have i₂ := b8e235 x y
               grind)
            | exact superpose b8e235 b8e361
            | (have j1 := b8e235 (σ x) (σ y)
               grind)
            | (have r₁ := b8e361
               have r₂ := b8e235 x y
               grind)
            | exact resolve b8e361 b8e235
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e361
          have b8e550 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
          clear b8e549
          have b8e553 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e550
               grind)
            | exact superpose b8e550 b8e20
            | exact resolve b8e20 b8e550
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e555 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e16 (σ y) (σ x)
               have i₂ := b8e550
               grind)
            | exact superpose b8e550 b8e16
            | exact resolve b8e16 b8e550
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e557 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b8e555
               have r₂ := b8e550
               grind)
            | exact resolve b8e555 b8e550
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e550 b8e555
          have b8e559 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e557
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e557
            | exact resolve b8e557 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e557
          have b8e693 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e235 x y
               have i₂ := b8e559
               grind)
            | exact superpose b8e559 b8e235
            | (have j0 := b8e235 x y
               grind)
            | exact resolve b8e235 b8e559
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e235 b8e559
          have b8e716 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
          clear b8e693
          have b8e737 : y = (M.op x y) := by
            first
            | (have r₁ := b8e716
               have r₂ := b8e553
               grind)
            | exact resolve b8e716 b8e553
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e553 b8e716
          have b8e817 : y ≠ (M.op x y) ∨ y = (k y x) := by
            first
            | (have i₁ := b8e16 y x
               have i₂ := b8e737
               grind)
            | exact superpose b8e737 b8e16
            | exact resolve b8e16 b8e737
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e819 : y = (k y x) := by
            first
            | (have r₁ := b8e817
               have r₂ := b8e737
               grind)
            | exact resolve b8e817 b8e737
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e817
          have b8e903 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e366 x y
               have i₂ := b8e819
               grind)
            | exact superpose b8e819 b8e366
            | (have j0 := b8e366 x y
               grind)
            | exact resolve b8e366 b8e819
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e366 b8e819
          have b8e907 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b8e903
          have b8e999 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e907
               grind)
            | exact superpose b8e907 b8e20
            | exact resolve b8e20 b8e907
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e907
          have b8e1004 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b8e999
               have i₂ := b8e737
               grind)
            | exact superpose b8e737 b8e999
            | exact resolve b8e999 b8e737
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e737 b8e999
          have b8e1005 : False := by grind
          exact b8e1005

/-- `Equation1`: `x = x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,m(Y,X)) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pypyx_y_x_y_pxy_pxx_pxy_Equation1 :
    AutBox.GuardAut2 ((Lf 1) ⋆ ((Lf 1) ⋆ (Lf 0))) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ ((Lf 1) ⋆ (Lf 0))) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b (M.op b a) ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b (M.op b a)) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b (M.op b a) = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b (M.op b a)) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b (M.op b a) = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b (M.op b a)) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y (M.op y x)) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (M.op (σ y) (σ x))) ((σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y (M.op y x)) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) := by grind
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
        have b1e15 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e25 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e19
          | exact resolve b1e19 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e26 : x = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 x
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
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e26
          | exact resolve b1e26 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e56 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          grind
        have b1e58 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e56 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56
        have b1e59 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e58 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e58
        have b1e63 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e59 (σ X0)
             grind)
          | exact superpose b1e59 b1e18
          | exact resolve b1e18 b1e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e63 X0
             have i₂ := b1e59 X0
             grind)
          | exact superpose b1e59 b1e63
          | exact resolve b1e63 b1e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59 b1e63
        have b1e127 : (σ (M.op x y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e25
             have i₂ := b1e66 y
             grind)
          | exact superpose b1e66 b1e25
          | exact resolve b1e25 b1e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e66
        have b1e135 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e127
             have i₂ := b1e27
             grind)
          | exact superpose b1e27 b1e127
          | exact resolve b1e127 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27 b1e127
        have b1e136 : False := by grind
        exact b1e136
      · have b2e15 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : y = (M.op y (M.op y x)) := by grind
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
        have b2e59 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X1 X0
             have i₂ := b2e17 X1 X0
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X1 X0
             have j1 := b2e17 (M.op X1 X0) (k X1 X0)
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 (M.op X1 (M.op X1 X0)) X1
             grind)
          | (have r₁ := b2e15 X0 X0
             have r₂ := b2e17 X0 (M.op X0 (M.op X0 X0))
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e61 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e59 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e59
        have b2e62 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e61 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61
        have b2e70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e62 (σ X1) (σ X0)
             grind)
          | exact superpose b2e62 b2e18
          | (have j1 := b2e62 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
             grind)
          | exact resolve b2e18 b2e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e62
        have b2e474 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
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
        have b2e486 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e474
             have r₂ := b2e22
             grind)
          | exact resolve b2e474 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e474
        have b2e491 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b2e486
             have i₂ := b2e40
             grind)
          | exact superpose b2e40 b2e486
          | exact resolve b2e486 b2e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40 b2e486
        have b2e492 : False := by grind
        exact b2e492
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (M.op (σ y) (σ x))) ((σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e21 : x = y := by grind
        have b3e22 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) := by grind
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
        have b3e46 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          grind
        have b3e48 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e46 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46
        have b3e49 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e48 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48
        have b3e77 : (σ (M.op y y)) ≠ (σ (k y y)) := by grind
        clear b3e36
        have b3e80 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e77
             have i₂ := b3e49 y
             grind)
          | exact superpose b3e49 b3e77
          | exact resolve b3e77 b3e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49 b3e77
        have b3e81 : False := by grind
        exact b3e81
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
          have b4e48 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e46 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46
          have b4e49 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e48 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48
          have b4e53 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e49 (σ X0)
               grind)
            | exact superpose b4e49 b4e19
            | exact resolve b4e19 b4e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e58 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e53 X0
               have i₂ := b4e49 X0
               grind)
            | exact superpose b4e49 b4e53
            | exact resolve b4e53 b4e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49 b4e53
          have b4e107 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
          clear b4e58
          have b4e112 : False := by grind
          exact b4e112
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (σ y) (M.op (σ y) (σ x))) ((σ y)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e21 : x ≠ y := by grind
        have b6e22 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) := by grind
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
        have b6e64 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e15 X1 X0
             have i₂ := b6e17 X1 X0
             grind)
          | exact superpose b6e17 b6e15
          | (have j0 := b6e15 X1 X0
             have j1 := b6e17 (M.op X1 X0) (k X1 X0)
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 (M.op X1 (M.op X1 X0)) X1
             grind)
          | (have r₁ := b6e15 X0 X0
             have r₂ := b6e17 X0 (M.op X0 (M.op X0 X0))
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e66 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e64 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64
        have b6e67 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e66 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e66
        have b6e77 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
          first
          | (have i₁ := b6e42
             have i₂ := b6e67 y x
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
        have b6e78 : x = y := by grind
        clear b6e77
        have b6e79 : False := by grind
        exact b6e79
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e22 : x ≠ y := by grind
          have b7e24 : (σ x) = (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e28 : x = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 x
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
               have i₂ := b7e14 y
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
          have b8e16 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
          have b8e58 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X1 X0
               have i₂ := b8e18 X1 X0
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X1 X0
               have j1 := b8e18 (M.op X1 X0) (k X1 X0)
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 (M.op X1 (M.op X1 X0)) X1
               grind)
            | (have r₁ := b8e16 X0 X0
               have r₂ := b8e18 X0 (M.op X0 (M.op X0 X0))
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e60 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e58 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e58
          have b8e61 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
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
               have i₂ := b8e61 (σ X1) (σ X0)
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
               have i₂ := b8e61 X1 (τ X0)
               grind)
            | exact superpose b8e61 b8e26
            | (have j1 := b8e61 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
               grind)
            | exact resolve b8e26 b8e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e61
          have b8e125 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
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
            | (have i₁ := b8e125 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e125
            | (have j0 := b8e125 (σ (k X0 X1)) (σ (M.op X0 X1))
               grind)
            | exact resolve b8e125 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e125
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
          have b8e483 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e471
               have r₂ := b8e24
               grind)
            | exact resolve b8e471 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e471
          have b8e491 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
            first
            | (have i₁ := b8e483
               have i₂ := b8e143 x y
               grind)
            | exact superpose b8e143 b8e483
            | (have j1 := b8e143 x y
               grind)
            | (have r₁ := b8e483
               have r₂ := b8e143 x y
               grind)
            | (have r₁ := b8e483
               have r₂ := b8e143 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e483
               have r₂ := b8e143 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e483 b8e143
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e143 b8e483
          have b8e492 : x = y := by grind
          clear b8e491
          have b8e494 : False := by grind
          exact b8e494
