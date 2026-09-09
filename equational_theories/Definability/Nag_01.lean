import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3671`: `x ◇ x = (x ◇ y) ◇ (z ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pxx_pyy_pxx_pyx_pxy_Equation3671 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3671 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3671.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (M.op y x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
    · rcases eq_or_ne (M.op y y) (M.op x y) with h2a | h2a
      · have b0e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X0 X1) (M.op X2 X1)) := by
          intro X0 X1 X2
          grind
        have b0e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b0e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b0e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : (M.op x x) = (M.op y x) := by grind
        have b0e21 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
        have b0e22 : (M.op x y) = (M.op y y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e31 : ∀ X0 : G, (M.op y y) = (M.op (M.op x x) (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b0e12 y x X0
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e12
          | exact resolve b0e12 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e32 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b0e12 y y x
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e12
          | exact resolve b0e12 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e41 : (M.op x y) = (M.op x x) := by
          first
          | (have i₁ := b0e32 x
             have i₂ := b0e12 x y x
             grind)
          | exact superpose b0e12 b0e32
          | exact resolve b0e32 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e32
        have b0e42 : (M.op x x) = (M.op y y) := by
          first
          | (have i₁ := b0e31 x
             have i₂ := b0e12 x x x
             grind)
          | exact superpose b0e12 b0e31
          | exact resolve b0e31 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e31
        have b0e46 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ x)) (M.op X0 (σ x))) := by
          intro X0
          first
          | (have i₁ := b0e12 (σ y) (σ x) X0
             have i₂ := b0e21
             grind)
          | exact superpose b0e21 b0e12
          | exact resolve b0e12 b0e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e47 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b0e46 x
             have i₂ := b0e12 (σ x) (σ x) x
             grind)
          | exact superpose b0e12 b0e46
          | exact resolve b0e46 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e46
        have b0e54 : ∀ X0 : G, (M.op x x) ≠ (M.op X0 y) ∨ (M.op x x) = (k y X0) := by
          intro X0
          first
          | (have i₁ := b0e15 y x
             have i₂ := b0e42
             grind)
          | exact superpose b0e42 b0e15
          | exact resolve b0e15 b0e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e42
        have b0e58 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b0e15 (σ x) (σ y)
             have i₂ := b0e21
             grind)
          | exact superpose b0e21 b0e15
          | (have j0 := b0e15 (σ x) (σ x)
             grind)
          | (have r₁ := b0e15 (σ x) (σ y)
             have r₂ := b0e21
             grind)
          | exact resolve b0e15 b0e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e59 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
          first
          | (have i₁ := b0e15 x y
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e15
          | (have j0 := b0e15 x x
             grind)
          | (have r₁ := b0e15 x y
             have r₂ := b0e20
             grind)
          | exact resolve b0e15 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e65 : (M.op x x) = (k x y) := by grind
        clear b0e59
        have b0e66 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b0e58
        have b0e70 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b0e66
             have i₂ := b0e18 x y
             grind)
          | exact superpose b0e18 b0e66
          | exact resolve b0e66 b0e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e66
        have b0e73 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b0e70
             have i₂ := b0e65
             grind)
          | exact superpose b0e65 b0e70
          | exact resolve b0e70 b0e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e65 b0e70
        have b0e230 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b0e16 (σ y) x
             have i₂ := b0e47
             grind)
          | exact superpose b0e47 b0e16
          | (have j0 := b0e16 X0 (σ x)
             grind)
          | (have r₁ := b0e16 (σ x) (σ y)
             have r₂ := b0e47
             grind)
          | (have r₁ := b0e16 (σ y) (σ x)
             have r₂ := b0e47
             grind)
          | exact resolve b0e16 b0e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e47
        have b0e246 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b0e230 X0
             have i₂ := b0e73
             grind)
          | exact superpose b0e73 b0e230
          | (have j0 := b0e230 X0
             grind)
          | exact resolve b0e230 b0e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e230
        have b0e253 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b0e246 X0
             have i₂ := b0e73
             grind)
          | exact superpose b0e73 b0e246
          | (have j0 := b0e246 X0
             grind)
          | (have r₁ := b0e246 (σ x)
             have r₂ := b0e73
             grind)
          | exact resolve b0e246 b0e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e246
        have b0e42834 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k y x) := by
          first
          | (have i₁ := b0e54 x
             have i₂ := b0e41
             grind)
          | exact superpose b0e41 b0e54
          | (have j0 := b0e54 x
             grind)
          | (have r₁ := b0e54 x
             have r₂ := b0e41
             grind)
          | exact resolve b0e54 b0e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e54
        have b0e42838 : (M.op x x) = (k y x) := by grind
        clear b0e42834
        have b0e513624 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b0e253 (σ x)
             have i₂ := b0e73
             grind)
          | exact superpose b0e73 b0e253
          | (have j0 := b0e253 (σ x)
             grind)
          | (have r₁ := b0e253 (σ x)
             have r₂ := b0e73
             grind)
          | exact resolve b0e253 b0e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e73 b0e253
        have b0e513692 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        clear b0e513624
        have b0e513703 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b0e513692
             have i₂ := b0e18 y x
             grind)
          | exact superpose b0e18 b0e513692
          | exact resolve b0e513692 b0e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e513692
        have b0e513704 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b0e513703
             have i₂ := b0e42838
             grind)
          | exact superpose b0e42838 b0e513703
          | exact resolve b0e513703 b0e42838
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e42838 b0e513703
        have b0e513705 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
        clear b0e513704
        have b0e513707 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e513705
             grind)
          | exact superpose b0e513705 b0e19
          | exact resolve b0e19 b0e513705
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e513705
        have b0e514043 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b0e513707
             have i₂ := b0e41
             grind)
          | exact superpose b0e41 b0e513707
          | exact resolve b0e513707 b0e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e41 b0e513707
        have b0e514044 : False := by grind
        exact b0e514044
      · rcases eq_or_ne (M.op y y) (M.op x x) with h2b | h2b
        · have b1e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X0 X1) (M.op X2 X1)) := by
            intro X0 X1 X2
            grind
          have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b1e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b1e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b1e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b1e21 : (M.op x x) = (M.op y x) := by grind
          have b1e22 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
          have b1e23 : (M.op x y) ≠ (M.op y y) := by grind
          have b1e24 : (M.op x x) = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e25 : (M.op x y) ≠ (M.op x x) := by
            first
            | (have i₁ := b1e23
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e23
            | exact resolve b1e23 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e46 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ x)) (M.op X0 (σ x))) := by
            intro X0
            first
            | (have i₁ := b1e13 (σ y) (σ x) X0
               have i₂ := b1e22
               grind)
            | exact superpose b1e22 b1e13
            | exact resolve b1e13 b1e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e47 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b1e46 x
               have i₂ := b1e13 (σ x) (σ x) x
               grind)
            | exact superpose b1e13 b1e46
            | exact resolve b1e46 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e46
          have b1e61 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b1e16 (σ x) (σ y)
               have i₂ := b1e22
               grind)
            | exact superpose b1e22 b1e16
            | (have j0 := b1e16 (σ x) (σ x)
               grind)
            | (have r₁ := b1e16 (σ x) (σ y)
               have r₂ := b1e22
               grind)
            | exact resolve b1e16 b1e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e62 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
            first
            | (have i₁ := b1e16 x y
               have i₂ := b1e21
               grind)
            | exact superpose b1e21 b1e16
            | (have j0 := b1e16 x x
               grind)
            | (have r₁ := b1e16 x y
               have r₂ := b1e21
               grind)
            | exact resolve b1e16 b1e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e66 : (M.op x x) = (k x y) := by grind
          clear b1e62
          have b1e67 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b1e61
          have b1e70 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b1e67
               have i₂ := b1e19 x y
               grind)
            | exact superpose b1e19 b1e67
            | exact resolve b1e67 b1e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e67
          have b1e72 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b1e70
               have i₂ := b1e66
               grind)
            | exact superpose b1e66 b1e70
            | exact resolve b1e70 b1e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e66 b1e70
          have b1e86 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op x x) = (M.op X0 y) ∨ (M.op X0 y) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b1e17 y x
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e17
            | (have j0 := b1e17 X0 x
               grind)
            | (have r₁ := b1e17 x y
               have r₂ := b1e24
               grind)
            | (have r₁ := b1e17 y x
               have r₂ := b1e24
               grind)
            | exact resolve b1e17 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e265 : ∀ X0 : G, (M.op (σ x) (σ x)) ≠ (M.op X0 (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b1e16 (σ y) x
               have i₂ := b1e47
               grind)
            | exact superpose b1e47 b1e16
            | exact resolve b1e16 b1e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e266 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b1e17 (σ y) x
               have i₂ := b1e47
               grind)
            | exact superpose b1e47 b1e17
            | (have j0 := b1e17 X0 (σ x)
               grind)
            | (have r₁ := b1e17 (σ x) (σ y)
               have r₂ := b1e47
               grind)
            | (have r₁ := b1e17 (σ y) (σ x)
               have r₂ := b1e47
               grind)
            | exact resolve b1e17 b1e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e47
          have b1e282 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b1e266 X0
               have i₂ := b1e72
               grind)
            | exact superpose b1e72 b1e266
            | (have j0 := b1e266 X0
               grind)
            | exact resolve b1e266 b1e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e266
          have b1e283 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op X0 (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b1e265 X0
               have i₂ := b1e72
               grind)
            | exact superpose b1e72 b1e265
            | (have j0 := b1e265 X0
               grind)
            | exact resolve b1e265 b1e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e265
          have b1e289 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b1e282 X0
               have i₂ := b1e72
               grind)
            | exact superpose b1e72 b1e282
            | (have j0 := b1e282 X0
               grind)
            | (have r₁ := b1e282 (σ x)
               have r₂ := b1e72
               grind)
            | exact resolve b1e282 b1e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e282
          have b1e290 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op X0 (σ y)) ∨ (σ (M.op x x)) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b1e283 X0
               have i₂ := b1e72
               grind)
            | exact superpose b1e72 b1e283
            | (have j0 := b1e283 X0
               grind)
            | exact resolve b1e283 b1e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e283
          have b1e3026 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (k y x) := by
            first
            | (have j0 := b1e86 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e86
          have b1e3028 : (M.op x y) = (k y x) := by
            first
            | (have r₁ := b1e3026
               have r₂ := b1e25
               grind)
            | exact resolve b1e3026 b1e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e25 b1e3026
          have b1e591723 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b1e289 (σ x)
               have i₂ := b1e72
               grind)
            | exact superpose b1e72 b1e289
            | (have j0 := b1e289 (σ x)
               grind)
            | (have r₁ := b1e289 (σ x)
               have r₂ := b1e72
               grind)
            | exact resolve b1e289 b1e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e72 b1e289
          have b1e591790 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
          clear b1e591723
          have b1e591801 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b1e591790
               have i₂ := b1e19 y x
               grind)
            | exact superpose b1e19 b1e591790
            | exact resolve b1e591790 b1e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e591790
          have b1e591802 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b1e591801
               have i₂ := b1e3028
               grind)
            | exact superpose b1e3028 b1e591801
            | exact resolve b1e591801 b1e3028
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e591801
          have b1e591803 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b1e591802
               have r₂ := b1e20
               grind)
            | exact resolve b1e591802 b1e20
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e591802
          have b1e591807 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b1e20
               have i₂ := b1e591803
               grind)
            | exact superpose b1e591803 b1e20
            | exact resolve b1e20 b1e591803
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e591824 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b1e290 (σ x)
               have i₂ := b1e591803
               grind)
            | exact superpose b1e591803 b1e290
            | (have j0 := b1e290 (σ x)
               grind)
            | (have r₁ := b1e290 (σ x)
               have r₂ := b1e591803
               grind)
            | exact resolve b1e290 b1e591803
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e290 b1e591803
          have b1e592024 : (σ (M.op x x)) = (k (σ y) (σ x)) := by grind
          clear b1e591824
          have b1e592140 : (σ (M.op x x)) = (σ (k y x)) := by
            first
            | (have i₁ := b1e592024
               have i₂ := b1e19 y x
               grind)
            | exact superpose b1e19 b1e592024
            | exact resolve b1e592024 b1e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e592024
          have b1e592203 : (σ (M.op x y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b1e592140
               have i₂ := b1e3028
               grind)
            | exact superpose b1e3028 b1e592140
            | exact resolve b1e592140 b1e3028
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e3028 b1e592140
          have b1e592231 : False := by grind
          exact b1e592231
        · have b2e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X0 X1) (M.op X2 X1)) := by
            intro X0 X1 X2
            grind
          have b2e21 : (M.op x x) = (M.op y x) := by grind
          have b2e24 : (M.op x x) ≠ (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e29 : ∀ X0 : G, (M.op y y) = (M.op (M.op x x) (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b2e13 y x X0
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e13
            | exact resolve b2e13 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e37 : (M.op x x) = (M.op y y) := by
            first
            | (have i₁ := b2e29 x
               have i₂ := b2e13 x x x
               grind)
            | exact superpose b2e13 b2e29
            | exact resolve b2e29 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e29
          have b2e38 : False := by grind
          exact b2e38
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
      · rcases eq_or_ne (M.op y y) (M.op x y) with h2a | h2a
        · have b3e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X0 X1) (M.op X2 X1)) := by
            intro X0 X1 X2
            grind
          have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b3e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b3e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b3e21 : (M.op x x) = (M.op y x) := by grind
          have b3e22 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
          have b3e23 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
          have b3e24 : (M.op x y) = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e34 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b3e13 y y x
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e13
            | exact resolve b3e13 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e43 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b3e34 x
               have i₂ := b3e13 x y x
               grind)
            | exact superpose b3e13 b3e34
            | exact resolve b3e34 b3e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e34
          have b3e68 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b3e16 (σ y) (σ y)
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e16
            | (have j0 := b3e16 (σ x) (σ x)
               grind)
            | exact resolve b3e16 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e69 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
            first
            | (have i₁ := b3e16 x y
               have i₂ := b3e21
               grind)
            | exact superpose b3e21 b3e16
            | (have j0 := b3e16 x x
               grind)
            | (have r₁ := b3e16 x y
               have r₂ := b3e21
               grind)
            | exact resolve b3e16 b3e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e72 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b3e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e75 : (M.op x x) = (k x y) := by grind
          clear b3e69
          have b3e76 : (M.op (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
          clear b3e68
          have b3e80 : (M.op (σ x) (σ x)) = (σ (k y y)) := by
            first
            | (have i₁ := b3e76
               have i₂ := b3e19 y y
               grind)
            | exact superpose b3e19 b3e76
            | exact resolve b3e76 b3e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e76
          have b3e83 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b3e80
               have i₂ := b3e72 y
               grind)
            | exact superpose b3e72 b3e80
            | exact resolve b3e80 b3e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e72 b3e80
          have b3e86 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b3e83
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e83
            | exact resolve b3e83 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e83
          have b3e87 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b3e86
               have i₂ := b3e43
               grind)
            | exact superpose b3e43 b3e86
            | exact resolve b3e86 b3e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e43 b3e86
          have b3e105 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b3e17 X0 (σ y)
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e17
            | (have j0 := b3e17 X0 (σ y)
               grind)
            | (have r₁ := b3e17 (σ x) (σ y)
               have r₂ := b3e23
               grind)
            | (have r₁ := b3e17 (σ y) (σ x)
               have r₂ := b3e23
               grind)
            | exact resolve b3e17 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e110 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x x)) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b3e105 X0
               have i₂ := b3e87
               grind)
            | exact superpose b3e87 b3e105
            | (have j0 := b3e105 X0
               grind)
            | exact resolve b3e105 b3e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e105
          have b3e6606 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b3e110 (σ x)
               have i₂ := b3e87
               grind)
            | exact superpose b3e87 b3e110
            | (have j0 := b3e110 (σ x)
               grind)
            | (have r₁ := b3e110 (σ x)
               have r₂ := b3e87
               grind)
            | exact resolve b3e110 b3e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e110
          have b3e6616 : (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b3e6606
          have b3e6619 : (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b3e6616
               have i₂ := b3e19 x y
               grind)
            | exact superpose b3e19 b3e6616
            | exact resolve b3e6616 b3e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e6616
          have b3e6631 : (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b3e6619
               have i₂ := b3e75
               grind)
            | exact superpose b3e75 b3e6619
            | exact resolve b3e6619 b3e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e75 b3e6619
          have b3e6632 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by grind
          clear b3e6631
          have b3e6665 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b3e22
               have i₂ := b3e6632
               grind)
            | exact superpose b3e6632 b3e22
            | exact resolve b3e22 b3e6632
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e6632
          have b3e6715 : False := by grind
          exact b3e6715
        · rcases eq_or_ne (M.op y y) (M.op x x) with h2b | h2b
          · have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b4e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b4e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b4e22 : (M.op x x) = (M.op y x) := by grind
            have b4e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
            have b4e24 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
            have b4e26 : (M.op x x) = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e71 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ y)) := by
              first
              | (have i₁ := b4e17 (σ y) (σ y)
                 have i₂ := b4e24
                 grind)
              | exact superpose b4e24 b4e17
              | (have j0 := b4e17 (σ x) (σ x)
                 grind)
              | exact resolve b4e17 b4e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e72 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
              first
              | (have i₁ := b4e17 x y
                 have i₂ := b4e22
                 grind)
              | exact superpose b4e22 b4e17
              | (have j0 := b4e17 x x
                 grind)
              | (have r₁ := b4e17 x y
                 have r₂ := b4e22
                 grind)
              | exact resolve b4e17 b4e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e74 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
              intro X0
              first
              | (have j0 := b4e17 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e76 : (M.op x x) = (k x y) := by grind
            clear b4e72
            have b4e77 : (M.op (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
            clear b4e71
            have b4e80 : (M.op (σ x) (σ x)) = (σ (k y y)) := by
              first
              | (have i₁ := b4e77
                 have i₂ := b4e20 y y
                 grind)
              | exact superpose b4e20 b4e77
              | exact resolve b4e77 b4e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e77
            have b4e82 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
              first
              | (have i₁ := b4e80
                 have i₂ := b4e74 y
                 grind)
              | exact superpose b4e74 b4e80
              | exact resolve b4e80 b4e74
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e74 b4e80
            have b4e84 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
              first
              | (have i₁ := b4e82
                 have i₂ := b4e26
                 grind)
              | exact superpose b4e26 b4e82
              | exact resolve b4e82 b4e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e82
            have b4e105 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b4e18 X0 (σ y)
                 have i₂ := b4e24
                 grind)
              | exact superpose b4e24 b4e18
              | (have j0 := b4e18 X0 (σ y)
                 grind)
              | (have r₁ := b4e18 (σ x) (σ y)
                 have r₂ := b4e24
                 grind)
              | (have r₁ := b4e18 (σ y) (σ x)
                 have r₂ := b4e24
                 grind)
              | exact resolve b4e18 b4e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e108 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x x)) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b4e105 X0
                 have i₂ := b4e84
                 grind)
              | exact superpose b4e84 b4e105
              | (have j0 := b4e105 X0
                 grind)
              | exact resolve b4e105 b4e84
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e105
            have b4e9425 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b4e108 (σ x)
                 have i₂ := b4e84
                 grind)
              | exact superpose b4e84 b4e108
              | (have j0 := b4e108 (σ x)
                 grind)
              | (have r₁ := b4e108 (σ x)
                 have r₂ := b4e84
                 grind)
              | exact resolve b4e108 b4e84
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e108
            have b4e9437 : (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
            clear b4e9425
            have b4e9440 : (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
              first
              | (have i₁ := b4e9437
                 have i₂ := b4e20 x y
                 grind)
              | exact superpose b4e20 b4e9437
              | exact resolve b4e9437 b4e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e9437
            have b4e9454 : (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
              first
              | (have i₁ := b4e9440
                 have i₂ := b4e76
                 grind)
              | exact superpose b4e76 b4e9440
              | exact resolve b4e9440 b4e76
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e76 b4e9440
            have b4e9455 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by grind
            clear b4e9454
            have b4e9490 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
              first
              | (have i₁ := b4e23
                 have i₂ := b4e9455
                 grind)
              | exact superpose b4e9455 b4e23
              | exact resolve b4e23 b4e9455
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e9455
            have b4e9545 : False := by grind
            exact b4e9545
          · have b5e14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X0 X1) (M.op X2 X1)) := by
              intro X0 X1 X2
              grind
            have b5e22 : (M.op x x) = (M.op y x) := by grind
            have b5e26 : (M.op x x) ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e31 : ∀ X0 : G, (M.op y y) = (M.op (M.op x x) (M.op X0 x)) := by
              intro X0
              first
              | (have i₁ := b5e14 y x X0
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e14
              | exact resolve b5e14 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e39 : (M.op x x) = (M.op y y) := by
              first
              | (have i₁ := b5e31 x
                 have i₂ := b5e14 x x x
                 grind)
              | exact superpose b5e14 b5e31
              | exact resolve b5e31 b5e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e31
            have b5e40 : False := by grind
            exact b5e40
      · rcases eq_or_ne (M.op y y) (M.op x y) with h2a | h2a
        · have b6e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X0 X1) (M.op X2 X1)) := by
            intro X0 X1 X2
            grind
          have b6e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b6e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b6e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          have b6e24 : (M.op x y) = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e34 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b6e13 y y x
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e13
            | exact resolve b6e13 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e43 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b6e34 x
               have i₂ := b6e13 x y x
               grind)
            | exact superpose b6e13 b6e34
            | exact resolve b6e34 b6e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e34
          have b6e68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b6e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e80 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b6e19 X0 X0
               have i₂ := b6e68 (σ X0)
               grind)
            | exact superpose b6e68 b6e19
            | exact resolve b6e19 b6e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e85 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b6e80 X0
               have i₂ := b6e68 X0
               grind)
            | exact superpose b6e68 b6e80
            | exact resolve b6e80 b6e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e68 b6e80
          have b6e428 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b6e23
               have i₂ := b6e85 y
               grind)
            | exact superpose b6e85 b6e23
            | exact resolve b6e23 b6e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e447 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b6e428
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e428
            | exact resolve b6e428 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e428
          have b6e450 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b6e447
               have i₂ := b6e85 x
               grind)
            | exact superpose b6e85 b6e447
            | exact resolve b6e447 b6e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e85 b6e447
          have b6e451 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b6e450
               have i₂ := b6e43
               grind)
            | exact superpose b6e43 b6e450
            | exact resolve b6e450 b6e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e43 b6e450
          have b6e452 : False := by grind
          exact b6e452
        · rcases eq_or_ne (M.op y y) (M.op x x) with h2b | h2b
          · have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b7e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b7e24 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
            have b7e26 : (M.op x x) = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e70 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
              intro X0
              first
              | (have j0 := b7e17 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e78 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have i₁ := b7e20 X0 X0
                 have i₂ := b7e70 (σ X0)
                 grind)
              | exact superpose b7e70 b7e20
              | exact resolve b7e20 b7e70
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e85 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b7e78 X0
                 have i₂ := b7e70 X0
                 grind)
              | exact superpose b7e70 b7e78
              | exact resolve b7e78 b7e70
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e70 b7e78
            have b7e227 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
              first
              | (have i₁ := b7e24
                 have i₂ := b7e85 y
                 grind)
              | exact superpose b7e85 b7e24
              | exact resolve b7e24 b7e85
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e240 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
              first
              | (have i₁ := b7e227
                 have i₂ := b7e26
                 grind)
              | exact superpose b7e26 b7e227
              | exact resolve b7e227 b7e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e227
            have b7e242 : False := by grind
            exact b7e242
          · have b8e14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X0 X1) (M.op X2 X1)) := by
              intro X0 X1 X2
              grind
            have b8e22 : (M.op x x) = (M.op y x) := by grind
            have b8e26 : (M.op x x) ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e31 : ∀ X0 : G, (M.op y y) = (M.op (M.op x x) (M.op X0 x)) := by
              intro X0
              first
              | (have i₁ := b8e14 y x X0
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e14
              | exact resolve b8e14 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e39 : (M.op x x) = (M.op y y) := by
              first
              | (have i₁ := b8e31 x
                 have i₂ := b8e14 x x x
                 grind)
              | exact superpose b8e14 b8e31
              | exact resolve b8e31 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e31
            have b8e40 : False := by grind
            exact b8e40
  · rcases eq_or_ne (M.op x x) (M.op y y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
      · rcases eq_or_ne (M.op y y) (M.op x y) with h2a | h2a
        · have b9e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b9e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b9e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b9e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b9e21 : (M.op x x) ≠ (M.op y x) := by grind
          have b9e22 : (M.op x x) = (M.op y y) := by grind
          have b9e23 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e73 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b9e16 (σ x) (σ y)
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e16
            | (have j0 := b9e16 (σ x) (σ x)
               grind)
            | (have r₁ := b9e16 (σ x) (σ y)
               have r₂ := b9e23
               grind)
            | exact resolve b9e16 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e76 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b9e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e79 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b9e73
          have b9e83 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b9e79
               have i₂ := b9e19 x y
               grind)
            | exact superpose b9e19 b9e79
            | exact resolve b9e79 b9e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e79
          have b9e109 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op X0 X0) = (M.op y X0) ∨ (M.op y X0) = (k X0 y) := by
            intro X0
            first
            | (have i₁ := b9e17 X0 y
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e17
            | (have j0 := b9e17 X0 y
               grind)
            | (have r₁ := b9e17 x y
               have r₂ := b9e22
               grind)
            | (have r₁ := b9e17 y x
               have r₂ := b9e22
               grind)
            | exact resolve b9e17 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e117 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
            first
            | (have i₁ := b9e16 (σ x) (σ x)
               have i₂ := b9e83
               grind)
            | exact superpose b9e83 b9e16
            | exact resolve b9e16 b9e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e83
          have b9e120 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
          clear b9e117
          have b9e121 : (σ (k x y)) = (σ (k x x)) := by
            first
            | (have i₁ := b9e120
               have i₂ := b9e19 x x
               grind)
            | exact superpose b9e19 b9e120
            | exact resolve b9e120 b9e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e120
          have b9e122 : (σ (k x y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b9e121
               have i₂ := b9e76 x
               grind)
            | exact superpose b9e76 b9e121
            | exact resolve b9e121 b9e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e76 b9e121
          have b9e234 : (k x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b9e14 (k x y)
               have i₂ := b9e122
               grind)
            | exact superpose b9e122 b9e14
            | exact resolve b9e14 b9e122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e122
          have b9e235 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b9e234
               have i₂ := b9e14 (M.op x x)
               grind)
            | exact superpose b9e14 b9e234
            | exact resolve b9e234 b9e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e234
          have b9e2741 : (M.op x x) = (M.op y x) ∨ (M.op y x) = (k x y) := by
            first
            | (have j0 := b9e109 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e109
          have b9e2742 : (M.op y x) = (k x y) := by
            first
            | (have r₁ := b9e2741
               have r₂ := b9e21
               grind)
            | exact resolve b9e2741 b9e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e2741
          have b9e2752 : (M.op x x) = (M.op y x) := by
            first
            | (have i₁ := b9e2742
               have i₂ := b9e235
               grind)
            | exact superpose b9e235 b9e2742
            | exact resolve b9e2742 b9e235
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e235 b9e2742
          have b9e2762 : False := by grind
          exact b9e2762
        · rcases eq_or_ne (M.op y y) (M.op x x) with h2b | h2b
          · have b10e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b10e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b10e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b10e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b10e22 : (M.op x x) ≠ (M.op y x) := by grind
            have b10e24 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
            have b10e26 : (M.op x x) = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e60 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b10e17 (σ x) (σ y)
                 have i₂ := b10e24
                 grind)
              | exact superpose b10e24 b10e17
              | (have j0 := b10e17 (σ x) (σ x)
                 grind)
              | (have r₁ := b10e17 (σ x) (σ y)
                 have r₂ := b10e24
                 grind)
              | exact resolve b10e17 b10e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e62 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
              intro X0
              first
              | (have j0 := b10e17 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e64 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
            clear b10e60
            have b10e67 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b10e64
                 have i₂ := b10e20 x y
                 grind)
              | exact superpose b10e20 b10e64
              | exact resolve b10e64 b10e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e64
            have b10e85 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op X0 X0) = (M.op y X0) ∨ (M.op y X0) = (k X0 y) := by
              intro X0
              first
              | (have i₁ := b10e18 X0 y
                 have i₂ := b10e26
                 grind)
              | exact superpose b10e26 b10e18
              | (have j0 := b10e18 X0 y
                 grind)
              | (have r₁ := b10e18 x y
                 have r₂ := b10e26
                 grind)
              | (have r₁ := b10e18 y x
                 have r₂ := b10e26
                 grind)
              | exact resolve b10e18 b10e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e90 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
              first
              | (have i₁ := b10e17 (σ x) (σ x)
                 have i₂ := b10e67
                 grind)
              | exact superpose b10e67 b10e17
              | exact resolve b10e17 b10e67
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e67
            have b10e93 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
            clear b10e90
            have b10e94 : (σ (k x y)) = (σ (k x x)) := by
              first
              | (have i₁ := b10e93
                 have i₂ := b10e20 x x
                 grind)
              | exact superpose b10e20 b10e93
              | exact resolve b10e93 b10e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e93
            have b10e95 : (σ (k x y)) = (σ (M.op x x)) := by
              first
              | (have i₁ := b10e94
                 have i₂ := b10e62 x
                 grind)
              | exact superpose b10e62 b10e94
              | exact resolve b10e94 b10e62
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e62 b10e94
            have b10e192 : (k x y) = (τ (σ (M.op x x))) := by
              first
              | (have i₁ := b10e15 (k x y)
                 have i₂ := b10e95
                 grind)
              | exact superpose b10e95 b10e15
              | exact resolve b10e15 b10e95
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e95
            have b10e193 : (M.op x x) = (k x y) := by
              first
              | (have i₁ := b10e192
                 have i₂ := b10e15 (M.op x x)
                 grind)
              | exact superpose b10e15 b10e192
              | exact resolve b10e192 b10e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e192
            have b10e2983 : (M.op x x) = (M.op y x) ∨ (M.op y x) = (k x y) := by
              first
              | (have j0 := b10e85 x
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e85
            have b10e2985 : (M.op y x) = (k x y) := by
              first
              | (have r₁ := b10e2983
                 have r₂ := b10e22
                 grind)
              | exact resolve b10e2983 b10e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e2983
            have b10e2995 : (M.op x x) = (M.op y x) := by
              first
              | (have i₁ := b10e2985
                 have i₂ := b10e193
                 grind)
              | exact superpose b10e193 b10e2985
              | exact resolve b10e2985 b10e193
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e193 b10e2985
            have b10e3005 : False := by grind
            exact b10e3005
          · have b11e23 : (M.op x x) = (M.op y y) := by grind
            have b11e26 : (M.op x x) ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e27 : False := by grind
            exact b11e27
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op y y) (M.op x y) with h2a | h2a
          · have b12e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b12e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b12e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b12e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b12e23 : (M.op x x) = (M.op y y) := by grind
            have b12e25 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
            have b12e26 : (M.op x y) = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e28 : (M.op x y) = (M.op x x) := by
              first
              | (have i₁ := b12e23
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e23
              | exact resolve b12e23 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e84 : ∀ X0 : G, (M.op x x) ≠ (M.op X0 y) ∨ (M.op x x) = (k y X0) := by
              intro X0
              first
              | (have i₁ := b12e17 y x
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e17
              | exact resolve b12e17 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e87 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ y)) := by
              first
              | (have i₁ := b12e17 (σ y) (σ y)
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e17
              | (have j0 := b12e17 (σ x) (σ x)
                 grind)
              | exact resolve b12e17 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e90 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
              intro X0
              first
              | (have j0 := b12e17 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e93 : (M.op (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
            clear b12e87
            have b12e97 : (M.op (σ x) (σ x)) = (σ (k y y)) := by
              first
              | (have i₁ := b12e93
                 have i₂ := b12e20 y y
                 grind)
              | exact superpose b12e20 b12e93
              | exact resolve b12e93 b12e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e93
            have b12e100 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
              first
              | (have i₁ := b12e97
                 have i₂ := b12e90 y
                 grind)
              | exact superpose b12e90 b12e97
              | exact resolve b12e97 b12e90
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e90 b12e97
            have b12e103 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b12e100
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e100
              | exact resolve b12e100 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e100
            have b12e104 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
              first
              | (have i₁ := b12e103
                 have i₂ := b12e28
                 grind)
              | exact superpose b12e28 b12e103
              | exact resolve b12e103 b12e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e103
            have b12e125 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b12e18 (σ y) x
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e18
              | (have j0 := b12e18 X0 (σ x)
                 grind)
              | (have r₁ := b12e18 (σ x) (σ y)
                 have r₂ := b12e25
                 grind)
              | (have r₁ := b12e18 (σ y) (σ x)
                 have r₂ := b12e25
                 grind)
              | exact resolve b12e18 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e137 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b12e125 X0
                 have i₂ := b12e104
                 grind)
              | exact superpose b12e104 b12e125
              | (have j0 := b12e125 X0
                 grind)
              | exact resolve b12e125 b12e104
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e125
            have b12e139 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x x)) ∨ (M.op X0 (σ y)) = (σ (M.op x x)) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b12e137 X0
                 have i₂ := b12e104
                 grind)
              | exact superpose b12e104 b12e137
              | (have j0 := b12e137 X0
                 grind)
              | (have r₁ := b12e137 (σ x)
                 have r₂ := b12e104
                 grind)
              | exact resolve b12e137 b12e104
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e137
            have b12e1050 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k y x) := by
              first
              | (have i₁ := b12e84 x
                 have i₂ := b12e28
                 grind)
              | exact superpose b12e28 b12e84
              | (have j0 := b12e84 x
                 grind)
              | (have r₁ := b12e84 x
                 have r₂ := b12e28
                 grind)
              | exact resolve b12e84 b12e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e84
            have b12e1053 : (M.op x x) = (k y x) := by grind
            clear b12e1050
            have b12e20360 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
              first
              | (have i₁ := b12e139 (σ x)
                 have i₂ := b12e104
                 grind)
              | exact superpose b12e104 b12e139
              | (have j0 := b12e139 (σ x)
                 grind)
              | (have r₁ := b12e139 (σ x)
                 have r₂ := b12e104
                 grind)
              | exact resolve b12e139 b12e104
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e104 b12e139
            have b12e20376 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
            clear b12e20360
            have b12e20380 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
              first
              | (have i₁ := b12e20376
                 have i₂ := b12e20 y x
                 grind)
              | exact superpose b12e20 b12e20376
              | exact resolve b12e20376 b12e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e20376
            have b12e20398 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
              first
              | (have i₁ := b12e20380
                 have i₂ := b12e1053
                 grind)
              | exact superpose b12e1053 b12e20380
              | exact resolve b12e20380 b12e1053
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e1053 b12e20380
            have b12e20399 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
            clear b12e20398
            have b12e20404 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
              first
              | (have i₁ := b12e21
                 have i₂ := b12e20399
                 grind)
              | exact superpose b12e20399 b12e21
              | exact resolve b12e21 b12e20399
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e20399
            have b12e20497 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
              first
              | (have i₁ := b12e20404
                 have i₂ := b12e28
                 grind)
              | exact superpose b12e28 b12e20404
              | exact resolve b12e20404 b12e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e28 b12e20404
            have b12e20498 : False := by grind
            exact b12e20498
          · rcases eq_or_ne (M.op y y) (M.op x x) with h2b | h2b
            · have b13e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b13e19 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b13e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b13e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b13e26 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
              have b13e27 : (M.op x y) ≠ (M.op y y) := by grind
              have b13e28 : (M.op x x) = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e29 : (M.op x y) ≠ (M.op x x) := by
                first
                | (have i₁ := b13e27
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e27
                | exact resolve b13e27 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e66 : ∀ X0 : G, (M.op (σ x) (σ x)) ≠ (M.op X0 (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ y) X0) := by
                intro X0
                first
                | (have i₁ := b13e18 (σ y) x
                   have i₂ := b13e26
                   grind)
                | exact superpose b13e26 b13e18
                | exact resolve b13e18 b13e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e70 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ y)) := by
                first
                | (have i₁ := b13e18 (σ y) (σ y)
                   have i₂ := b13e26
                   grind)
                | exact superpose b13e26 b13e18
                | (have j0 := b13e18 (σ x) (σ x)
                   grind)
                | exact resolve b13e18 b13e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e72 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have j0 := b13e18 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e74 : (M.op (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
              clear b13e70
              have b13e77 : (M.op (σ x) (σ x)) = (σ (k y y)) := by
                first
                | (have i₁ := b13e74
                   have i₂ := b13e21 y y
                   grind)
                | exact superpose b13e21 b13e74
                | exact resolve b13e74 b13e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e74
              have b13e79 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
                first
                | (have i₁ := b13e77
                   have i₂ := b13e72 y
                   grind)
                | exact superpose b13e72 b13e77
                | exact resolve b13e77 b13e72
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e72 b13e77
              have b13e81 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
                first
                | (have i₁ := b13e79
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e79
                | exact resolve b13e79 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e79
              have b13e98 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
                intro X0
                first
                | (have i₁ := b13e19 (σ y) x
                   have i₂ := b13e26
                   grind)
                | exact superpose b13e26 b13e19
                | (have j0 := b13e19 X0 (σ x)
                   grind)
                | (have r₁ := b13e19 (σ x) (σ y)
                   have r₂ := b13e26
                   grind)
                | (have r₁ := b13e19 (σ y) (σ x)
                   have r₂ := b13e26
                   grind)
                | exact resolve b13e19 b13e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e99 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op x x) = (M.op X0 y) ∨ (M.op X0 y) = (k y X0) := by
                intro X0
                first
                | (have i₁ := b13e19 y x
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e19
                | (have j0 := b13e19 X0 x
                   grind)
                | (have r₁ := b13e19 x y
                   have r₂ := b13e28
                   grind)
                | (have r₁ := b13e19 y x
                   have r₂ := b13e28
                   grind)
                | exact resolve b13e19 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e106 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
                intro X0
                first
                | (have i₁ := b13e98 X0
                   have i₂ := b13e81
                   grind)
                | exact superpose b13e81 b13e98
                | (have j0 := b13e98 X0
                   grind)
                | exact resolve b13e98 b13e81
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e98
              have b13e107 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x x)) ∨ (M.op X0 (σ y)) = (σ (M.op x x)) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
                intro X0
                first
                | (have i₁ := b13e106 X0
                   have i₂ := b13e81
                   grind)
                | exact superpose b13e81 b13e106
                | (have j0 := b13e106 X0
                   grind)
                | (have r₁ := b13e106 (σ x)
                   have r₂ := b13e81
                   grind)
                | exact resolve b13e106 b13e81
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e106
              have b13e4564 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (k y x) := by
                first
                | (have j0 := b13e99 x
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e99
              have b13e4566 : (M.op x y) = (k y x) := by
                first
                | (have r₁ := b13e4564
                   have r₂ := b13e29
                   grind)
                | exact resolve b13e4564 b13e29
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e29 b13e4564
              have b13e21167 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
                first
                | (have i₁ := b13e107 (σ x)
                   have i₂ := b13e81
                   grind)
                | exact superpose b13e81 b13e107
                | (have j0 := b13e107 (σ x)
                   grind)
                | (have r₁ := b13e107 (σ x)
                   have r₂ := b13e81
                   grind)
                | exact resolve b13e107 b13e81
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e107
              have b13e21183 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
              clear b13e21167
              have b13e21187 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
                first
                | (have i₁ := b13e21183
                   have i₂ := b13e21 y x
                   grind)
                | exact superpose b13e21 b13e21183
                | exact resolve b13e21183 b13e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e21183
              have b13e21206 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
                first
                | (have i₁ := b13e21187
                   have i₂ := b13e4566
                   grind)
                | exact superpose b13e4566 b13e21187
                | exact resolve b13e21187 b13e4566
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e21187
              have b13e21209 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
                first
                | (have r₁ := b13e21206
                   have r₂ := b13e22
                   grind)
                | exact resolve b13e21206 b13e22
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e21206
              have b13e21210 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
                first
                | (have i₁ := b13e22
                   have i₂ := b13e21209
                   grind)
                | exact superpose b13e21209 b13e22
                | exact resolve b13e22 b13e21209
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e21215 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
                first
                | (have i₁ := b13e66 (σ x)
                   have i₂ := b13e21209
                   grind)
                | exact superpose b13e21209 b13e66
                | (have j0 := b13e66 (σ x)
                   grind)
                | exact resolve b13e66 b13e21209
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e66 b13e21209
              have b13e21303 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
                first
                | (have r₁ := b13e21215
                   have r₂ := b13e81
                   grind)
                | exact resolve b13e21215 b13e81
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e21215
              have b13e21319 : (M.op (σ x) (σ x)) = (σ (k y x)) := by
                first
                | (have i₁ := b13e21303
                   have i₂ := b13e21 y x
                   grind)
                | exact superpose b13e21 b13e21303
                | exact resolve b13e21303 b13e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e21303
              have b13e21325 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
                first
                | (have i₁ := b13e21319
                   have i₂ := b13e4566
                   grind)
                | exact superpose b13e4566 b13e21319
                | exact resolve b13e21319 b13e4566
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e4566 b13e21319
              have b13e21330 : (σ (M.op x y)) = (σ (M.op x x)) := by
                first
                | (have i₁ := b13e21325
                   have i₂ := b13e81
                   grind)
                | exact superpose b13e81 b13e21325
                | exact resolve b13e21325 b13e81
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e81 b13e21325
              have b13e21331 : False := by grind
              exact b13e21331
            · have b14e24 : (M.op x x) = (M.op y y) := by grind
              have b14e28 : (M.op x x) ≠ (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e29 : False := by grind
              exact b14e29
        · rcases eq_or_ne (M.op y y) (M.op x y) with h2a | h2a
          · have b15e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b15e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b15e23 : (M.op x x) = (M.op y y) := by grind
            have b15e25 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
            have b15e26 : (M.op x y) = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e28 : (M.op x y) = (M.op x x) := by
              first
              | (have i₁ := b15e23
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e23
              | exact resolve b15e23 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e86 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
              intro X0
              first
              | (have j0 := b15e17 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e97 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have i₁ := b15e20 X0 X0
                 have i₂ := b15e86 (σ X0)
                 grind)
              | exact superpose b15e86 b15e20
              | exact resolve b15e20 b15e86
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e106 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b15e97 X0
                 have i₂ := b15e86 X0
                 grind)
              | exact superpose b15e86 b15e97
              | exact resolve b15e97 b15e86
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e86 b15e97
            have b15e130 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
              first
              | (have i₁ := b15e25
                 have i₂ := b15e106 y
                 grind)
              | exact superpose b15e106 b15e25
              | exact resolve b15e25 b15e106
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e140 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b15e130
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e130
              | exact resolve b15e130 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e130
            have b15e141 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
              first
              | (have i₁ := b15e140
                 have i₂ := b15e106 x
                 grind)
              | exact superpose b15e106 b15e140
              | exact resolve b15e140 b15e106
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e106 b15e140
            have b15e142 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
              first
              | (have i₁ := b15e141
                 have i₂ := b15e28
                 grind)
              | exact superpose b15e28 b15e141
              | exact resolve b15e141 b15e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e28 b15e141
            have b15e143 : False := by grind
            exact b15e143
          · rcases eq_or_ne (M.op y y) (M.op x x) with h2b | h2b
            · have b16e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b16e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b16e26 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
              have b16e28 : (M.op x x) = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have j0 := b16e18 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e75 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b16e21 X0 X0
                   have i₂ := b16e68 (σ X0)
                   grind)
                | exact superpose b16e68 b16e21
                | exact resolve b16e21 b16e68
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e82 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b16e75 X0
                   have i₂ := b16e68 X0
                   grind)
                | exact superpose b16e68 b16e75
                | exact resolve b16e75 b16e68
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e68 b16e75
              have b16e208 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
                first
                | (have i₁ := b16e26
                   have i₂ := b16e82 y
                   grind)
                | exact superpose b16e82 b16e26
                | exact resolve b16e26 b16e82
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e221 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
                first
                | (have i₁ := b16e208
                   have i₂ := b16e28
                   grind)
                | exact superpose b16e28 b16e208
                | exact resolve b16e208 b16e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e208
              have b16e223 : False := by grind
              exact b16e223
            · have b17e24 : (M.op x x) = (M.op y y) := by grind
              have b17e28 : (M.op x x) ≠ (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e29 : False := by grind
              exact b17e29
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
      · rcases eq_or_ne (M.op y y) (M.op x y) with h2a | h2a
        · have b18e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X0 X1) (M.op X2 X1)) := by
            intro X0 X1 X2
            grind
          have b18e22 : (M.op x x) ≠ (M.op y y) := by grind
          have b18e24 : (M.op x y) = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e25 : (M.op x y) ≠ (M.op x x) := by
            first
            | (have i₁ := b18e22
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e22
            | exact resolve b18e22 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e30 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b18e13 y y x
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e13
            | exact resolve b18e13 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e38 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b18e30 x
               have i₂ := b18e13 x y x
               grind)
            | exact superpose b18e13 b18e30
            | exact resolve b18e30 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e30
          have b18e39 : False := by grind
          exact b18e39
        · rcases eq_or_ne (M.op y y) (M.op x x) with h2b | h2b
          · have b19e23 : (M.op x x) ≠ (M.op y y) := by grind
            have b19e26 : (M.op x x) = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e28 : False := by grind
            exact b19e28
          · have b20e14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X0 X1) (M.op X2 X1)) := by
              intro X0 X1 X2
              grind
            have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b20e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b20e24 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
            have b20e26 : (M.op x x) ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e42 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ x)) (M.op X0 (σ x))) := by
              intro X0
              first
              | (have i₁ := b20e14 (σ y) (σ x) X0
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e14
              | exact resolve b20e14 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e43 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b20e42 x
                 have i₂ := b20e14 (σ x) (σ x) x
                 grind)
              | exact superpose b20e14 b20e42
              | exact resolve b20e42 b20e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e42
            have b20e57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
              intro X0
              first
              | (have j0 := b20e17 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e64 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have i₁ := b20e20 X0 X0
                 have i₂ := b20e57 (σ X0)
                 grind)
              | exact superpose b20e57 b20e20
              | exact resolve b20e20 b20e57
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e69 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b20e64 X0
                 have i₂ := b20e57 X0
                 grind)
              | exact superpose b20e57 b20e64
              | exact resolve b20e64 b20e57
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e64
            have b20e197 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ y)) := by
              first
              | (have i₁ := b20e17 (σ y) (σ y)
                 have i₂ := b20e43
                 grind)
              | exact superpose b20e43 b20e17
              | (have j0 := b20e17 (σ x) (σ x)
                 grind)
              | exact resolve b20e17 b20e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e43
            have b20e200 : (M.op (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
            clear b20e197
            have b20e203 : (M.op (σ x) (σ x)) = (σ (k y y)) := by
              first
              | (have i₁ := b20e200
                 have i₂ := b20e20 y y
                 grind)
              | exact superpose b20e20 b20e200
              | exact resolve b20e200 b20e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e200
            have b20e214 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
              first
              | (have i₁ := b20e203
                 have i₂ := b20e57 y
                 grind)
              | exact superpose b20e57 b20e203
              | exact resolve b20e203 b20e57
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e57 b20e203
            have b20e223 : (σ (M.op x x)) = (σ (M.op y y)) := by
              first
              | (have i₁ := b20e214
                 have i₂ := b20e69 x
                 grind)
              | exact superpose b20e69 b20e214
              | exact resolve b20e214 b20e69
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e69 b20e214
            have b20e438 : (M.op y y) = (τ (σ (M.op x x))) := by
              first
              | (have i₁ := b20e15 (M.op y y)
                 have i₂ := b20e223
                 grind)
              | exact superpose b20e223 b20e15
              | exact resolve b20e15 b20e223
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e223
            have b20e439 : (M.op x x) = (M.op y y) := by
              first
              | (have i₁ := b20e438
                 have i₂ := b20e15 (M.op x x)
                 grind)
              | exact superpose b20e15 b20e438
              | exact resolve b20e438 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e438
            have b20e442 : False := by grind
            exact b20e442
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op y y) (M.op x y) with h2a | h2a
          · have b21e14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X0 X1) (M.op X2 X1)) := by
              intro X0 X1 X2
              grind
            have b21e23 : (M.op x x) ≠ (M.op y y) := by grind
            have b21e26 : (M.op x y) = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e27 : (M.op x y) ≠ (M.op x x) := by
              first
              | (have i₁ := b21e23
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e23
              | exact resolve b21e23 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e32 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op X0 y)) := by
              intro X0
              first
              | (have i₁ := b21e14 y y x
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e14
              | exact resolve b21e14 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e40 : (M.op x y) = (M.op x x) := by
              first
              | (have i₁ := b21e32 x
                 have i₂ := b21e14 x y x
                 grind)
              | exact superpose b21e14 b21e32
              | exact resolve b21e32 b21e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e32
            have b21e41 : False := by grind
            exact b21e41
          · rcases eq_or_ne (M.op y y) (M.op x x) with h2b | h2b
            · have b22e24 : (M.op x x) ≠ (M.op y y) := by grind
              have b22e28 : (M.op x x) = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e30 : False := by grind
              exact b22e30
            · have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e26 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
              have b23e28 : (M.op x x) ≠ (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e66 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ y)) := by
                first
                | (have i₁ := b23e18 (σ y) (σ y)
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e18
                | (have j0 := b23e18 (σ x) (σ x)
                   grind)
                | exact resolve b23e18 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have j0 := b23e18 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e68 : (M.op (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
              clear b23e66
              have b23e70 : (M.op (σ x) (σ x)) = (σ (k y y)) := by
                first
                | (have i₁ := b23e68
                   have i₂ := b23e21 y y
                   grind)
                | exact superpose b23e21 b23e68
                | exact resolve b23e68 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e68
              have b23e72 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
                first
                | (have i₁ := b23e70
                   have i₂ := b23e67 y
                   grind)
                | exact superpose b23e67 b23e70
                | exact resolve b23e70 b23e67
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e70
              have b23e101 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (k (σ x) (σ x)) := by
                first
                | (have i₁ := b23e18 (σ x) (σ x)
                   have i₂ := b23e72
                   grind)
                | exact superpose b23e72 b23e18
                | exact resolve b23e18 b23e72
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e72
              have b23e104 : (σ (M.op y y)) = (k (σ x) (σ x)) := by grind
              clear b23e101
              have b23e105 : (σ (M.op y y)) = (σ (k x x)) := by
                first
                | (have i₁ := b23e104
                   have i₂ := b23e21 x x
                   grind)
                | exact superpose b23e21 b23e104
                | exact resolve b23e104 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e104
              have b23e106 : (σ (M.op y y)) = (σ (M.op x x)) := by
                first
                | (have i₁ := b23e105
                   have i₂ := b23e67 x
                   grind)
                | exact superpose b23e67 b23e105
                | exact resolve b23e105 b23e67
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e67 b23e105
              have b23e230 : (M.op y y) = (τ (σ (M.op x x))) := by
                first
                | (have i₁ := b23e16 (M.op y y)
                   have i₂ := b23e106
                   grind)
                | exact superpose b23e106 b23e16
                | exact resolve b23e16 b23e106
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e106
              have b23e231 : (M.op x x) = (M.op y y) := by
                first
                | (have i₁ := b23e230
                   have i₂ := b23e16 (M.op x x)
                   grind)
                | exact superpose b23e16 b23e230
                | exact resolve b23e230 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e230
              have b23e235 : False := by grind
              exact b23e235
        · rcases eq_or_ne (M.op y y) (M.op x y) with h2a | h2a
          · have b24e14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X0 X1) (M.op X2 X1)) := by
              intro X0 X1 X2
              grind
            have b24e23 : (M.op x x) ≠ (M.op y y) := by grind
            have b24e26 : (M.op x y) = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e27 : (M.op x y) ≠ (M.op x x) := by
              first
              | (have i₁ := b24e23
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e23
              | exact resolve b24e23 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e32 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op X0 y)) := by
              intro X0
              first
              | (have i₁ := b24e14 y y x
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e14
              | exact resolve b24e14 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e40 : (M.op x y) = (M.op x x) := by
              first
              | (have i₁ := b24e32 x
                 have i₂ := b24e14 x y x
                 grind)
              | exact superpose b24e14 b24e32
              | exact resolve b24e32 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e32
            have b24e41 : False := by grind
            exact b24e41
          · rcases eq_or_ne (M.op y y) (M.op x x) with h2b | h2b
            · have b25e24 : (M.op x x) ≠ (M.op y y) := by grind
              have b25e28 : (M.op x x) = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e30 : False := by grind
              exact b25e30
            · have b26e15 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X0 X1) (M.op X2 X1)) := by
                intro X0 X1 X2
                grind
              have b26e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b26e20 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e23 : (M.op x x) ≠ (M.op y x) := by grind
              have b26e26 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
              have b26e28 : (M.op x x) ≠ (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
                intro X0
                first
                | (have j0 := b26e18 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b26e21 X0 X0
                   have i₂ := b26e63 (σ X0)
                   grind)
                | exact superpose b26e63 b26e21
                | exact resolve b26e21 b26e63
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e75 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b26e68 X0
                   have i₂ := b26e63 X0
                   grind)
                | exact superpose b26e63 b26e68
                | exact resolve b26e68 b26e63
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e63 b26e68
              have b26e130 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X0)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e15 X1 X0 X2
                   have i₂ := b26e20 X0 X1
                   grind)
                | (have i₁ := b26e15 X0 X0 X2
                   have i₂ := b26e20 X0 X1
                   grind)
                | exact superpose b26e20 b26e15
                | (have j1 := b26e20 X0 X1
                   grind)
                | exact resolve b26e15 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e152 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op X0 X0) = (M.op y X0) ∨ (M.op X0 y) = (k X0 y) := by
                intro X0
                first
                | (have i₁ := b26e28
                   have i₂ := b26e20 X0 y
                   grind)
                | (have i₁ := b26e28
                   have i₂ := b26e20 y x
                   grind)
                | exact superpose b26e20 b26e28
                | (have j1 := b26e20 X0 y
                   grind)
                | (have r₁ := b26e28
                   have r₂ := b26e20 x y
                   grind)
                | (have r₁ := b26e28
                   have r₂ := b26e20 y x
                   grind)
                | exact resolve b26e28 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e174 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
                intro X0 X1
                first
                | (have i₁ := b26e130 X0 X1 x
                   have i₂ := b26e15 X0 X0 x
                   grind)
                | exact superpose b26e15 b26e130
                | (have j0 := b26e130 X0 X1 x
                   grind)
                | exact resolve b26e130 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e130
              have b26e175 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
                intro X0 X1
                first
                | (have j0 := b26e174 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e174
              have b26e197 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
                first
                | (have i₁ := b26e26
                   have i₂ := b26e75 y
                   grind)
                | exact superpose b26e75 b26e26
                | exact resolve b26e26 b26e75
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e210 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
                first
                | (have i₁ := b26e197
                   have i₂ := b26e75 x
                   grind)
                | exact superpose b26e75 b26e197
                | exact resolve b26e197 b26e75
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e197
              have b26e773 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e21 X0 X1
                   have i₂ := b26e175 (σ X0) (σ X1)
                   grind)
                | exact superpose b26e175 b26e21
                | (have j1 := b26e175 (σ X0) (σ X1)
                   grind)
                | exact resolve b26e21 b26e175
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e175
              have b26e786 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e773 X0 X1
                   have i₂ := b26e75 X1
                   grind)
                | exact superpose b26e75 b26e773
                | (have j0 := b26e773 X0 X1
                   grind)
                | exact resolve b26e773 b26e75
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e773
              have b26e808 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e786 X0 X1
                   have i₂ := b26e75 X0
                   grind)
                | exact superpose b26e75 b26e786
                | (have j0 := b26e786 X0 X1
                   grind)
                | exact resolve b26e786 b26e75
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e75 b26e786
              have b26e2900 : (M.op x x) = (M.op y x) ∨ (M.op x y) = (k x y) := by
                first
                | (have j0 := b26e152 x
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e152
              have b26e2901 : (M.op x y) = (k x y) := by
                first
                | (have r₁ := b26e2900
                   have r₂ := b26e23
                   grind)
                | exact resolve b26e2900 b26e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2900
              have b26e174870 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e808 x y
                   grind)
                | exact superpose b26e808 b26e22
                | (have j1 := b26e808 x y
                   grind)
                | exact resolve b26e22 b26e808
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e808
              have b26e175187 : (σ (M.op x y)) ≠ (σ (k x y)) := by
                first
                | (have r₁ := b26e174870
                   have r₂ := b26e210
                   grind)
                | exact resolve b26e174870 b26e210
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e210 b26e174870
              have b26e175407 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
                first
                | (have i₁ := b26e175187
                   have i₂ := b26e2901
                   grind)
                | exact superpose b26e2901 b26e175187
                | exact resolve b26e175187 b26e2901
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2901 b26e175187
              have b26e175408 : False := by grind
              exact b26e175408

/-- `Equation3740`: `x ◇ y = (x ◇ z) ◇ (z ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pxy_x_pxy_Equation3740 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3740 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3740.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op x x) := by grind
      have b0e20 : (σ x) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e39 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k x X0) := by
        intro X0
        first
        | (have i₁ := b0e14 x X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 x X0
           grind)
        | (have r₁ := b0e14 x x
           have r₂ := b0e19
           grind)
        | exact resolve b0e14 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e40 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e14 (σ x) X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have j0 := b0e14 (σ x) X0
           grind)
        | (have r₁ := b0e14 (σ x) x
           have r₂ := b0e20
           grind)
        | exact resolve b0e14 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e43 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) := by
        intro X0
        first
        | (have j0 := b0e40 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40
      have b0e44 : ∀ X0 : G, (M.op x X0) = (k x X0) := by
        intro X0
        first
        | (have j0 := b0e39 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e76 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 x X0
           have i₂ := b0e43 (σ X0)
           grind)
        | exact superpose b0e43 b0e17
        | exact resolve b0e17 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43
      have b0e77 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
        intro X0
        first
        | (have i₁ := b0e76 X0
           have i₂ := b0e44 X0
           grind)
        | exact superpose b0e44 b0e76
        | exact resolve b0e76 b0e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44 b0e76
      have b0e210 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e77 y
           grind)
        | exact superpose b0e77 b0e18
        | (have r₁ := b0e18
           have r₂ := b0e77 y
           grind)
        | exact resolve b0e18 b0e77
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e77
      have b0e219 : False := by grind
      exact b0e219
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op x x) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e37 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k x X0) := by
          intro X0
          first
          | (have i₁ := b1e15 x X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e15
          | (have j0 := b1e15 x X0
             grind)
          | (have r₁ := b1e15 x x
             have r₂ := b1e20
             grind)
          | exact resolve b1e15 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e42 : ∀ X0 : G, (M.op x X0) = (k x X0) := by
          intro X0
          first
          | (have j0 := b1e37 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e64 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e21
             have i₂ := b1e17 X0 (σ x)
             grind)
          | exact superpose b1e17 b1e21
          | (have j1 := b1e17 X0 X0
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e17 (σ x) x
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e17 X0 (σ x)
             grind)
          | exact resolve b1e21 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e66 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
          intro X0
          first
          | (have j0 := b1e64 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e64
        have b1e72 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) := by
          intro X0
          first
          | (have j0 := b1e66 X0
             have j1 := b1e15 X0 (σ x)
             grind)
          | (have r₁ := b1e66 X0
             have r₂ := b1e15 X0 x
             grind)
          | exact resolve b1e66 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e66
        have b1e80 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 x
             have i₂ := b1e72 (σ X0)
             grind)
          | exact superpose b1e72 b1e18
          | exact resolve b1e18 b1e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e72
        have b1e1285 : (σ x) ≠ (σ (k x x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e80 x
             grind)
          | exact superpose b1e80 b1e21
          | exact resolve b1e21 b1e80
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e80
        have b1e1314 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e1285
             have i₂ := b1e42 x
             grind)
          | exact superpose b1e42 b1e1285
          | exact resolve b1e1285 b1e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42 b1e1285
        have b1e1328 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e1314
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1314
          | exact resolve b1e1314 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1314
        have b1e1329 : False := by grind
        exact b1e1329
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : x = (M.op x x) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e35 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k x X0) := by
          intro X0
          first
          | (have i₁ := b2e15 x X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e15
          | (have j0 := b2e15 x X0
             grind)
          | (have r₁ := b2e15 x x
             have r₂ := b2e20
             grind)
          | exact resolve b2e15 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e38 : ∀ X0 : G, (M.op x X0) = (k x X0) := by
          intro X0
          first
          | (have j0 := b2e35 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35
        have b2e60 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e22
             have i₂ := b2e17 X0 (σ y)
             grind)
          | exact superpose b2e17 b2e22
          | (have j1 := b2e17 X0 X0
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e17 (σ y) x
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e17 X0 (σ y)
             grind)
          | exact resolve b2e22 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e62 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b2e60 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e60
        have b2e70 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b2e62 X0
             have j1 := b2e15 X0 (σ y)
             grind)
          | (have r₁ := b2e62 X0
             have r₂ := b2e15 X0 x
             grind)
          | exact resolve b2e62 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e62
        have b2e77 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 y
             have i₂ := b2e70 (σ X0)
             grind)
          | exact superpose b2e70 b2e18
          | exact resolve b2e18 b2e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e70
        have b2e253 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e77 x
             grind)
          | exact superpose b2e77 b2e19
          | exact resolve b2e19 b2e77
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e77
        have b2e266 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b2e253
             have i₂ := b2e38 y
             grind)
          | exact superpose b2e38 b2e253
          | exact resolve b2e253 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38 b2e253
        have b2e267 : False := by grind
        exact b2e267
  · rcases eq_or_ne (M.op y y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : x ≠ (M.op x x) := by grind
        have b3e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e38 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b3e15 (σ x) X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e15
          | (have j0 := b3e15 (σ x) X0
             grind)
          | (have r₁ := b3e15 (σ x) x
             have r₂ := b3e22
             grind)
          | exact resolve b3e15 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e41 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have j0 := b3e38 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38
        have b3e73 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 x X0
             have i₂ := b3e41 (σ X0)
             grind)
          | exact superpose b3e41 b3e18
          | exact resolve b3e18 b3e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e41
        have b3e175 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e73 x
             grind)
          | exact superpose b3e73 b3e22
          | exact resolve b3e22 b3e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e73
        have b3e217 : (k x x) = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e175
             grind)
          | exact superpose b3e175 b3e13
          | exact resolve b3e13 b3e175
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e175
        have b3e219 : x = (k x x) := by
          first
          | (have i₁ := b3e217
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e217
          | exact resolve b3e217 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e217
        have b3e238 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e17 x x
             have i₂ := b3e219
             grind)
          | exact superpose b3e219 b3e17
          | (have j0 := b3e17 x x
             grind)
          | exact resolve b3e17 b3e219
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e219
        have b3e239 : x = (M.op x x) := by grind
        clear b3e238
        have b3e241 : False := by grind
        exact b3e241
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X2 X1)) := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ (M.op x x) := by grind
          have b4e22 : y = (M.op y y) := by grind
          have b4e23 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b4e29 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e19 (k (τ X0) X1) X2
               have i₂ := b4e25 X0 X1
               grind)
            | exact superpose b4e25 b4e19
            | exact resolve b4e19 b4e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k (τ X0) X1)
               have i₂ := b4e25 X0 X1
               grind)
            | exact superpose b4e25 b4e14
            | exact resolve b4e14 b4e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e31 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b4e13 y X0 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e32 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ y) X0 (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op (M.op X2 X1) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 (M.op X0 X2) X3 (M.op X2 X1)
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op X0 (σ y)) (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 (M.op X0 X3)) (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X2 (M.op X3 X1) (M.op X0 X3)
               have i₂ := b4e13 X0 X1 X3
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39 : ∀ X0 X1 : G, (M.op X1 (M.op y X0)) = (M.op (M.op X1 y) (M.op y X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 (M.op y X0) y
               have i₂ := b4e31 X0
               grind)
            | exact superpose b4e31 b4e13
            | exact resolve b4e13 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31
          have b4e42 : ∀ X0 X1 : G, (M.op X1 (M.op y X0)) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e39 X0 X1
               have i₂ := b4e13 X1 X0 y
               grind)
            | exact superpose b4e13 b4e39
            | exact resolve b4e39 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e43 : ∀ X0 : G, y ≠ y ∨ (M.op y X0) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b4e16 y X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e16
            | (have j0 := b4e16 y X0
               grind)
            | (have r₁ := b4e16 y x
               have r₂ := b4e22
               grind)
            | exact resolve b4e16 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e44 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) X0) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e16 (σ y) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | (have j0 := b4e16 (σ y) X0
               grind)
            | (have r₁ := b4e16 (σ y) x
               have r₂ := b4e24
               grind)
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 (M.op X0 X0) X1
               have i₂ := b4e13 X0 X0 X0
               grind)
            | exact superpose b4e13 b4e16
            | (have j0 := b4e16 (M.op X0 X0) X1
               grind)
            | (have r₁ := b4e16 (M.op X1 X1) X1
               have r₂ := b4e13 X1 X1 X1
               grind)
            | exact resolve b4e16 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e46 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
            intro X0 X1
            first
            | (have j0 := b4e45 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45
          have b4e47 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) := by
            intro X0
            first
            | (have j0 := b4e44 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44
          have b4e48 : ∀ X0 : G, (M.op y X0) = (k y X0) := by
            intro X0
            first
            | (have j0 := b4e43 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43
          have b4e68 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e17 X1 X0
               have i₂ := b4e18 X2 X0
               grind)
            | exact superpose b4e18 b4e17
            | (have j0 := b4e17 X1 X0
               have j1 := b4e18 X1 X1
               grind)
            | (have r₁ := b4e17 X0 X0
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | exact resolve b4e17 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e69 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e16 X0 X1
               have i₂ := b4e18 X2 X0
               grind)
            | exact superpose b4e18 b4e16
            | (have j0 := b4e16 X0 X1
               have j1 := b4e18 X2 X2
               grind)
            | (have r₁ := b4e16 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e16 X1 X1
               have r₂ := b4e18 X0 X1
               grind)
            | exact resolve b4e16 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e70 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e23
               have i₂ := b4e18 X0 (σ x)
               grind)
            | exact superpose b4e18 b4e23
            | (have j1 := b4e18 X0 X0
               grind)
            | (have r₁ := b4e23
               have r₂ := b4e18 (σ x) x
               grind)
            | (have r₁ := b4e23
               have r₂ := b4e18 X0 (σ x)
               grind)
            | exact resolve b4e23 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e73 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
            intro X0
            first
            | (have j0 := b4e70 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e70
          have b4e74 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e69 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e69
          have b4e75 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e68 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e68
          have b4e79 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) := by
            intro X0
            first
            | (have j0 := b4e73 X0
               have j1 := b4e16 X0 (σ x)
               grind)
            | (have r₁ := b4e73 X0
               have r₂ := b4e16 X0 x
               grind)
            | exact resolve b4e73 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e73
          have b4e80 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X2 X0) = (k X2 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e74 X0 X1 X2
               have j1 := b4e16 X0 X1
               grind)
            | (have r₁ := b4e74 X0 X1 X0
               have r₂ := b4e16 X0 X1
               grind)
            | exact resolve b4e74 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e74
          have b4e81 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X0) = (k X2 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e75 X0 X1 X1
               have j1 := b4e16 X2 X0
               grind)
            | (have r₁ := b4e75 X0 X0 X2
               have r₂ := b4e16 X0 X1
               grind)
            | (have r₁ := b4e75 X0 X1 X0
               have r₂ := b4e16 X0 X1
               grind)
            | exact resolve b4e75 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e75
          have b4e85 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 y X0
               have i₂ := b4e47 (σ X0)
               grind)
            | exact superpose b4e47 b4e19
            | exact resolve b4e19 b4e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e86 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b4e85 X0
               have i₂ := b4e48 X0
               grind)
            | exact superpose b4e48 b4e85
            | exact resolve b4e85 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e85
          have b4e89 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 x
               have i₂ := b4e79 (σ X0)
               grind)
            | exact superpose b4e79 b4e19
            | exact resolve b4e19 b4e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e100 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 X1 y
               have i₂ := b4e42 X1 (M.op X0 y)
               grind)
            | exact superpose b4e42 b4e13
            | exact resolve b4e13 b4e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e111 : ∀ X0 : G, (k (σ (σ y)) X0) = (σ (M.op (σ y) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e26 X0 (σ y)
               have i₂ := b4e47 (τ X0)
               grind)
            | exact superpose b4e47 b4e26
            | exact resolve b4e26 b4e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e112 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op y (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e26 X0 y
               have i₂ := b4e48 (τ X0)
               grind)
            | exact superpose b4e48 b4e26
            | exact resolve b4e26 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26 b4e48
          have b4e121 : ∀ X0 : G, (M.op (σ y) X0) = (σ (M.op y (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e112 X0
               have i₂ := b4e47 X0
               grind)
            | exact superpose b4e47 b4e112
            | exact resolve b4e112 b4e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e47 b4e112
          have b4e208 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e30 X1 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e30
            | exact resolve b4e30 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e211 : ∀ X0 : G, (k (τ X0) x) = (τ (M.op X0 (σ x))) := by
            intro X0
            first
            | (have i₁ := b4e30 X0 x
               have i₂ := b4e79 X0
               grind)
            | exact superpose b4e79 b4e30
            | exact resolve b4e30 b4e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e214 : ∀ X0 X1 : G, (k (τ (M.op X0 X0)) X1) = (τ (M.op (M.op X0 X0) (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e30 (M.op X0 X0) X1
               have i₂ := b4e46 X0 (σ X1)
               grind)
            | exact superpose b4e46 b4e30
            | exact resolve b4e30 b4e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e231 : ∀ X0 X1 : G, (M.op X1 (M.op (σ y) X0)) = (M.op (M.op X1 (σ y)) (M.op (σ y) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 (M.op (σ y) X0) (σ y)
               have i₂ := b4e32 X0
               grind)
            | exact superpose b4e32 b4e13
            | exact resolve b4e13 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e234 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op (σ y) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e231 X0 X1
               have i₂ := b4e13 X1 X0 (σ y)
               grind)
            | exact superpose b4e13 b4e231
            | exact resolve b4e231 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e231
          have b4e274 : (σ x) ≠ (σ (k x x)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e89 x
               grind)
            | exact superpose b4e89 b4e23
            | exact resolve b4e23 b4e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e284 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (k X0 x)) (M.op (σ x) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (σ X0) X1 (σ x)
               have i₂ := b4e89 X0
               grind)
            | exact superpose b4e89 b4e13
            | exact resolve b4e13 b4e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e89
          have b4e386 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e80 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e80
          have b4e387 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e386 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e386
          have b4e398 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e387 (σ X0)
               grind)
            | exact superpose b4e387 b4e19
            | exact resolve b4e19 b4e387
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e399 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e25 X0 (τ X0)
               have i₂ := b4e387 (τ X0)
               grind)
            | exact superpose b4e387 b4e25
            | exact resolve b4e25 b4e387
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e407 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e399 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e399
            | exact resolve b4e399 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e399
          have b4e408 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e398 X0
               have i₂ := b4e387 X0
               grind)
            | exact superpose b4e387 b4e398
            | exact resolve b4e398 b4e387
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e398
          have b4e412 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e407 X0
               have i₂ := b4e387 X0
               grind)
            | exact superpose b4e387 b4e407
            | exact resolve b4e407 b4e387
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e407
          have b4e454 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X0) (M.op (M.op X1 X4) X2)) = (M.op (M.op X3 X4) (M.op (M.op X0 X1) X2)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e33 X3 X4 X0 (M.op (M.op X1 X4) X2)
               have i₂ := b4e33 X0 X4 X1 X2
               grind)
            | exact superpose b4e33 b4e33
            | exact resolve b4e33 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e455 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (σ y)) = (M.op (M.op X1 (σ y)) (M.op X0 (σ y))) := by
            intro X0 X1
            first
            | (have i₁ := b4e33 X1 (σ y) X0 (σ y)
               have i₂ := b4e35 X0
               grind)
            | exact superpose b4e35 b4e33
            | exact resolve b4e33 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e471 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (M.op (M.op X1 y) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e100 X0 (M.op (M.op X1 y) X2)
               have i₂ := b4e33 X0 y X1 X2
               grind)
            | exact superpose b4e33 b4e100
            | exact resolve b4e100 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e476 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X1) X2) = (k (M.op (M.op (M.op X0 X1) X0) X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e46 (M.op (M.op X2 x) x) X1
               have i₂ := b4e33 (M.op X2 x) x X2 x
               grind)
            | exact superpose b4e33 b4e46
            | exact resolve b4e46 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33
          have b4e486 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e471 X0 X1 X2
               have i₂ := b4e100 X1 X2
               grind)
            | exact superpose b4e100 b4e471
            | exact resolve b4e471 b4e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e471
          have b4e615 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 X3)) = (M.op (M.op X2 (M.op X0 X1)) (M.op (M.op X0 y) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e36 (M.op X0 y) X3 X2 X1
               have i₂ := b4e100 X0 X1
               grind)
            | exact superpose b4e100 b4e36
            | exact resolve b4e36 b4e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e672 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 (M.op X0 X1))) X2) = (k (M.op X0 (M.op X1 (M.op X0 X1))) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e46 (M.op X0 (M.op X0 x)) X1
               have i₂ := b4e36 X0 (M.op X0 x) X0 x
               grind)
            | exact superpose b4e36 b4e46
            | exact resolve b4e46 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e686 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X1 (M.op X0 X1))) X2) = (M.op X0 (M.op (M.op X1 (M.op X0 X1)) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e672 X0 X1 X2
               have i₂ := b4e486 X0 (M.op X1 (M.op X0 X1)) X2
               grind)
            | exact superpose b4e486 b4e672
            | exact resolve b4e672 b4e486
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e672
          have b4e735 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 X3)) = (M.op (M.op X2 y) (M.op (M.op (M.op X0 X1) X0) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e615 X0 X1 X2 X3
               have i₂ := b4e454 (M.op X0 X1) X0 X3 X2 y
               grind)
            | (have i₁ := b4e615 X0 X1 X3 X2
               have i₂ := b4e454 X0 y X2 X3 (M.op X0 X1)
               grind)
            | exact superpose b4e454 b4e615
            | exact resolve b4e615 b4e454
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e454 b4e615
          have b4e747 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X1 (M.op X0 X1))) X2) = (M.op X0 (M.op X1 (M.op (M.op X0 X1) X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e686 X0 X1 X2
               have i₂ := b4e486 X1 (M.op X0 X1) X2
               grind)
            | exact superpose b4e486 b4e686
            | exact resolve b4e686 b4e486
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e686
          have b4e786 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 X3)) = (M.op X2 (M.op y (M.op (M.op (M.op X0 X1) X0) X3))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e735 X0 X1 X2 X3
               have i₂ := b4e486 X2 y (M.op (M.op (M.op X0 X1) X0) X3)
               grind)
            | exact superpose b4e486 b4e735
            | exact resolve b4e735 b4e486
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e735
          have b4e793 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X1 (M.op X0 X1))) X2) = (M.op X0 (M.op X1 (M.op X0 (M.op X1 X2)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e747 X0 X1 X2
               have i₂ := b4e486 X0 X1 X2
               grind)
            | exact superpose b4e486 b4e747
            | exact resolve b4e747 b4e486
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e747
          have b4e813 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 X3)) = (M.op X2 (M.op (M.op (M.op X0 X1) X0) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e786 X0 X1 X2 X3
               have i₂ := b4e42 (M.op (M.op (M.op X0 X1) X0) X3) X2
               grind)
            | exact superpose b4e42 b4e786
            | exact resolve b4e786 b4e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e786
          have b4e831 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 X3)) = (M.op X2 (M.op (M.op X0 X1) (M.op X0 X3))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e813 X0 X1 X2 X3
               have i₂ := b4e486 (M.op X0 X1) X0 X3
               grind)
            | exact superpose b4e486 b4e813
            | exact resolve b4e813 b4e486
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e813
          have b4e847 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 X3)) = (M.op X2 (M.op X0 (M.op X1 (M.op X0 X3)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e831 X0 X1 X2 X3
               have i₂ := b4e486 X0 X1 (M.op X0 X3)
               grind)
            | exact superpose b4e486 b4e831
            | exact resolve b4e831 b4e486
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e831
          have b4e1238 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ x = (M.op x x) ∨ (M.op X0 x) = (k X0 x) := by
            intro X0
            first
            | (have i₁ := b4e274
               have i₂ := b4e81 x x X0
               grind)
            | exact superpose b4e81 b4e274
            | (have j1 := b4e81 x x X0
               grind)
            | exact resolve b4e274 b4e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e81 b4e274
          have b4e1253 : ∀ X0 : G, x = (M.op x x) ∨ (M.op X0 x) = (k X0 x) := by
            intro X0
            first
            | (have j0 := b4e1238 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1238
          have b4e1261 : ∀ X0 : G, (M.op X0 x) = (k X0 x) := by
            intro X0
            first
            | (have j0 := b4e1253 X0
               grind)
            | (have r₁ := b4e1253 X0
               have r₂ := b4e21
               grind)
            | exact resolve b4e1253 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1253
          have b4e1296 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op (τ X0) x)) := by
            intro X0
            first
            | (have i₁ := b4e25 X0 x
               have i₂ := b4e1261 (τ X0)
               grind)
            | exact superpose b4e1261 b4e25
            | exact resolve b4e25 b4e1261
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25
          have b4e1298 : ∀ X0 : G, (M.op X0 (σ x)) = (σ (M.op (τ X0) x)) := by
            intro X0
            first
            | (have i₁ := b4e1296 X0
               have i₂ := b4e79 X0
               grind)
            | exact superpose b4e79 b4e1296
            | exact resolve b4e1296 b4e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e79 b4e1296
          have b4e1415 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e387 (τ X0)
               have i₂ := b4e208 X0 X0
               grind)
            | exact superpose b4e208 b4e387
            | exact resolve b4e387 b4e208
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e208
          have b4e1426 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e1415 X0
               have i₂ := b4e387 X0
               grind)
            | exact superpose b4e387 b4e1415
            | exact resolve b4e1415 b4e387
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e387 b4e1415
          have b4e1558 : ∀ X0 : G, (τ (M.op X0 (σ x))) = (k (τ (M.op X0 y)) x) := by
            intro X0
            first
            | (have i₁ := b4e211 (M.op X0 y)
               have i₂ := b4e100 X0 (σ x)
               grind)
            | exact superpose b4e100 b4e211
            | exact resolve b4e211 b4e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1577 : ∀ X0 : G, (τ (M.op X0 (σ x))) = (M.op (τ (M.op X0 y)) x) := by
            intro X0
            first
            | (have i₁ := b4e1558 X0
               have i₂ := b4e1261 (τ (M.op X0 y))
               grind)
            | exact superpose b4e1261 b4e1558
            | exact resolve b4e1558 b4e1261
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1558
          have b4e1581 : ∀ X0 : G, (k (τ X0) x) = (M.op (τ (M.op X0 y)) x) := by
            intro X0
            first
            | (have i₁ := b4e1577 X0
               have i₂ := b4e211 X0
               grind)
            | exact superpose b4e211 b4e1577
            | exact resolve b4e1577 b4e211
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e211 b4e1577
          have b4e1583 : ∀ X0 : G, (M.op (τ X0) x) = (M.op (τ (M.op X0 y)) x) := by
            intro X0
            first
            | (have i₁ := b4e1581 X0
               have i₂ := b4e1261 (τ X0)
               grind)
            | exact superpose b4e1261 b4e1581
            | exact resolve b4e1581 b4e1261
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1581
          have b4e2220 : ∀ X0 X1 : G, (k (M.op X0 X0) (σ X1)) = (σ (k (M.op (τ X0) (τ X0)) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 (M.op (τ X0) (τ X0)) X1
               have i₂ := b4e412 X0
               grind)
            | exact superpose b4e412 b4e19
            | exact resolve b4e19 b4e412
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e412
          have b4e2239 : ∀ X0 X1 : G, (k (M.op X0 X0) (σ X1)) = (σ (M.op (M.op (τ X0) (τ X0)) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e2220 X0 X1
               have i₂ := b4e46 (τ X0) X1
               grind)
            | exact superpose b4e46 b4e2220
            | exact resolve b4e2220 b4e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2220
          have b4e2256 : ∀ X0 X1 : G, (k (M.op X0 X0) (σ X1)) = (σ (M.op (τ X0) (M.op (τ X0) X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e2239 X0 X1
               have i₂ := b4e486 (τ X0) (τ X0) X1
               grind)
            | exact superpose b4e486 b4e2239
            | exact resolve b4e2239 b4e486
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2239
          have b4e2261 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ X1)) = (σ (M.op (τ X0) (M.op (τ X0) X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e2256 X0 X1
               have i₂ := b4e46 X0 (σ X1)
               grind)
            | exact superpose b4e46 b4e2256
            | exact resolve b4e2256 b4e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2256
          have b4e2263 : ∀ X0 X1 : G, (σ (M.op (τ X0) (M.op (τ X0) X1))) = (M.op X0 (M.op X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e2261 X0 X1
               have i₂ := b4e486 X0 X0 (σ X1)
               grind)
            | exact superpose b4e486 b4e2261
            | exact resolve b4e2261 b4e486
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2261
          have b4e2380 : ∀ X0 : G, (σ (M.op y (M.op (σ y) (τ X0)))) = (M.op (σ y) (k (σ (σ y)) X0)) := by
            intro X0
            first
            | (have i₁ := b4e86 (M.op (σ y) (τ X0))
               have i₂ := b4e111 X0
               grind)
            | exact superpose b4e111 b4e86
            | exact resolve b4e86 b4e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e86 b4e111
          have b4e2389 : ∀ X0 : G, (σ (M.op y (τ X0))) = (M.op (σ y) (k (σ (σ y)) X0)) := by
            intro X0
            first
            | (have i₁ := b4e2380 X0
               have i₂ := b4e234 (τ X0) y
               grind)
            | exact superpose b4e234 b4e2380
            | exact resolve b4e2380 b4e234
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2380
          have b4e2406 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (k (σ (σ y)) X0)) := by
            intro X0
            first
            | (have i₁ := b4e2389 X0
               have i₂ := b4e121 X0
               grind)
            | exact superpose b4e121 b4e2389
            | exact resolve b4e2389 b4e121
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e121 b4e2389
          have b4e2436 : ∀ X0 X1 : G, (k (τ (M.op X0 X0)) X1) = (M.op (τ (M.op X0 X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e46 (τ X0) X1
               have i₂ := b4e1426 X0
               grind)
            | exact superpose b4e1426 b4e46
            | exact resolve b4e46 b4e1426
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2448 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (M.op (τ (M.op X0 X0)) (M.op (τ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (τ X0) X1 (τ X0)
               have i₂ := b4e1426 X0
               grind)
            | exact superpose b4e1426 b4e13
            | exact resolve b4e13 b4e1426
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2748 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e1298 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e1298
            | exact resolve b4e1298 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1298
          have b4e3690 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ x) X1)) = (M.op (σ (M.op X0 x)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e486 (σ X0) (σ x) X1
               have i₂ := b4e2748 X0
               grind)
            | exact superpose b4e2748 b4e486
            | exact resolve b4e486 b4e2748
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2748
          have b4e3696 : ∀ X0 X1 : G, (M.op (τ X0) (M.op (τ X0) X1)) = (M.op (τ (M.op X0 X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e486 (τ X0) (τ X0) X1
               have i₂ := b4e1426 X0
               grind)
            | exact superpose b4e1426 b4e486
            | exact resolve b4e486 b4e1426
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1426
          have b4e3732 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op X1 (M.op X1 X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X0 X2 X1
               have i₂ := b4e486 X0 X1 (M.op X1 X2)
               grind)
            | exact superpose b4e486 b4e13
            | exact resolve b4e13 b4e486
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e3992 : ∀ X0 X1 : G, (M.op (τ (M.op X0 y)) (M.op x X1)) = (M.op (M.op (τ X0) x) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e486 (τ (M.op X0 y)) x X1
               have i₂ := b4e1583 X0
               grind)
            | exact superpose b4e1583 b4e486
            | exact resolve b4e486 b4e1583
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e3994 : ∀ X0 X1 : G, (M.op (τ (M.op X0 y)) (M.op x X1)) = (M.op (τ X0) (M.op x X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e3992 X0 X1
               have i₂ := b4e486 (τ X0) x X1
               grind)
            | exact superpose b4e486 b4e3992
            | exact resolve b4e3992 b4e486
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3992
          have b4e4247 : ∀ X0 X1 X2 : G, (σ (k (k (τ (M.op X0 X0)) X1) X2)) = (k (M.op (M.op X0 X0) (σ X1)) (σ X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e29 (M.op X0 X0) X1 X2
               have i₂ := b4e46 X0 (σ X1)
               grind)
            | exact superpose b4e46 b4e29
            | exact resolve b4e29 b4e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29
          have b4e4331 : ∀ X0 X1 X2 : G, (σ (k (k (τ (M.op X0 X0)) X1) X2)) = (k (M.op X0 (M.op X0 (σ X1))) (σ X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e4247 X0 X1 X2
               have i₂ := b4e486 X0 X0 (σ X1)
               grind)
            | exact superpose b4e486 b4e4247
            | exact resolve b4e4247 b4e486
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4247
          have b4e4354 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X0 (σ X1))) (σ X2)) = (σ (k (M.op (τ (M.op X0 X0)) X1) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e4331 X0 X1 X2
               have i₂ := b4e2436 X0 X1
               grind)
            | exact superpose b4e2436 b4e4331
            | exact resolve b4e4331 b4e2436
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4331
          have b4e11646 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (σ y)) X1) = (k (M.op (M.op X0 X0) (σ y)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e46 (M.op X0 (σ y)) X1
               have i₂ := b4e455 X0 X0
               grind)
            | exact superpose b4e455 b4e46
            | exact resolve b4e46 b4e455
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46
          have b4e11736 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 (σ y))) X1) = (k (M.op X0 (M.op X0 (σ y))) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e11646 X1 X1
               have i₂ := b4e486 X1 X1 (σ y)
               grind)
            | exact superpose b4e486 b4e11646
            | exact resolve b4e11646 b4e486
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e11646
          have b4e11810 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 (σ y)) X1)) = (k (M.op X0 (M.op X0 (σ y))) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e11736 X0 X1
               have i₂ := b4e486 X0 (M.op X0 (σ y)) X1
               grind)
            | exact superpose b4e486 b4e11736
            | exact resolve b4e11736 b4e486
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e11736
          have b4e11865 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (σ y) X1))) = (k (M.op X0 (M.op X0 (σ y))) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e11810 X0 X1
               have i₂ := b4e486 X0 (σ y) X1
               grind)
            | exact superpose b4e486 b4e11810
            | exact resolve b4e11810 b4e486
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e11810
          have b4e11902 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k (M.op X0 (M.op X0 (σ y))) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e11865 X0 X1
               have i₂ := b4e234 X1 X0
               grind)
            | exact superpose b4e234 b4e11865
            | exact resolve b4e11865 b4e234
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e11865
          have b4e28779 : ∀ X0 X1 X2 : G, (k (τ (M.op (M.op (M.op X0 X1) X0) X1)) X2) = (τ (M.op (M.op (M.op (M.op X0 X1) X0) X1) (σ X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e30 (M.op (M.op (M.op X0 X1) X0) X1) X2
               have i₂ := b4e476 X0 X1 (σ X2)
               grind)
            | exact superpose b4e476 b4e30
            | exact resolve b4e30 b4e476
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e476
          have b4e28788 : ∀ X0 X1 X2 : G, (k (τ (M.op (M.op (M.op X0 X1) X0) X1)) X2) = (τ (M.op (M.op (M.op X0 X1) X0) (M.op X1 (σ X2)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e28779 X0 X1 X2
               have i₂ := b4e486 (M.op (M.op X0 X1) X0) X1 (σ X2)
               grind)
            | exact superpose b4e486 b4e28779
            | exact resolve b4e28779 b4e486
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28779
          have b4e28948 : ∀ X0 X1 X2 : G, (k (τ (M.op (M.op (M.op X0 X1) X0) X1)) X2) = (τ (M.op (M.op X0 X1) (M.op X0 (M.op X1 (σ X2))))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e28788 X0 X1 X2
               have i₂ := b4e486 (M.op X0 X1) X0 (M.op X1 (σ X2))
               grind)
            | exact superpose b4e486 b4e28788
            | exact resolve b4e28788 b4e486
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28788
          have b4e29105 : ∀ X0 X1 X2 : G, (k (τ (M.op (M.op (M.op X0 X1) X0) X1)) X2) = (τ (M.op X0 (M.op X1 (M.op X0 (M.op X1 (σ X2)))))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e28948 X0 X1 X2
               have i₂ := b4e486 X0 X1 (M.op X0 (M.op X1 (σ X2)))
               grind)
            | exact superpose b4e486 b4e28948
            | exact resolve b4e28948 b4e486
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28948
          have b4e29254 : ∀ X0 X1 X2 : G, (k (τ (M.op (M.op (M.op X0 X1) X0) X1)) X2) = (τ (M.op X0 (M.op X0 (σ X2)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e29105 X0 X1 X2
               have i₂ := b4e847 X1 X0 X0 (σ X2)
               grind)
            | exact superpose b4e847 b4e29105
            | exact resolve b4e29105 b4e847
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29105
          have b4e29395 : ∀ X0 X1 X2 : G, (τ (M.op X0 (M.op X0 (σ X2)))) = (k (τ (M.op (M.op X0 X1) (M.op X0 X1))) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e29254 X0 X1 X2
               have i₂ := b4e486 (M.op X0 X1) X0 X1
               grind)
            | exact superpose b4e486 b4e29254
            | exact resolve b4e29254 b4e486
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29254
          have b4e29507 : ∀ X0 X1 X2 : G, (τ (M.op X0 (M.op X0 (σ X2)))) = (M.op (τ (M.op (M.op X0 X1) (M.op X0 X1))) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e29395 X0 X1 X2
               have i₂ := b4e2436 (M.op X0 X1) X2
               grind)
            | exact superpose b4e2436 b4e29395
            | exact resolve b4e29395 b4e2436
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29395
          have b4e29609 : ∀ X0 X1 X2 : G, (τ (M.op X0 (M.op X0 (σ X2)))) = (M.op (τ (M.op X0 (M.op X1 (M.op X0 X1)))) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e29507 X0 X1 X2
               have i₂ := b4e486 X0 X1 (M.op X0 X1)
               grind)
            | exact superpose b4e486 b4e29507
            | exact resolve b4e29507 b4e486
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29507
          have b4e35511 : ∀ X0 X1 : G, (M.op (τ (M.op X0 y)) (M.op x (M.op (τ (M.op X0 y)) (M.op x X1)))) = (k (M.op (τ (M.op X0 y)) (M.op x (M.op (τ X0) x))) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e793 (τ (M.op X0 y)) x X1
               have i₂ := b4e1583 X0
               grind)
            | exact superpose b4e1583 b4e793
            | exact resolve b4e793 b4e1583
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1583
          have b4e35830 : ∀ X0 X1 : G, (k (M.op (τ X0) (M.op x (M.op (τ X0) x))) X1) = (M.op (τ (M.op X0 y)) (M.op x (M.op (τ (M.op X0 y)) (M.op x X1)))) := by
            intro X0 X1
            first
            | (have i₁ := b4e35511 X0 X1
               have i₂ := b4e3994 X0 (M.op (τ X0) x)
               grind)
            | exact superpose b4e3994 b4e35511
            | exact resolve b4e35511 b4e3994
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3994 b4e35511
          have b4e36030 : ∀ X0 X1 : G, (k (M.op (τ X0) (M.op x (M.op (τ X0) x))) X1) = (M.op (τ (M.op X0 y)) (M.op (τ (M.op X0 y)) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e35830 X0 X1
               have i₂ := b4e847 x (τ (M.op X0 y)) (τ (M.op X0 y)) X1
               grind)
            | exact superpose b4e847 b4e35830
            | exact resolve b4e35830 b4e847
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35830
          have b4e36193 : ∀ X0 X1 : G, (k (M.op (τ X0) (M.op x (M.op (τ X0) x))) X1) = (M.op (τ (M.op (M.op X0 y) (M.op X0 y))) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e36030 X0 X1
               have i₂ := b4e3696 (M.op X0 y) X1
               grind)
            | exact superpose b4e3696 b4e36030
            | exact resolve b4e36030 b4e3696
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36030
          have b4e36336 : ∀ X0 X1 : G, (k (M.op (τ X0) (M.op x (M.op (τ X0) x))) X1) = (M.op (τ (M.op X0 (M.op y (M.op X0 y)))) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e36193 X0 X1
               have i₂ := b4e486 X0 y (M.op X0 y)
               grind)
            | exact superpose b4e486 b4e36193
            | exact resolve b4e36193 b4e486
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36193
          have b4e36431 : ∀ X0 X1 : G, (k (M.op (τ X0) (M.op x (M.op (τ X0) x))) X1) = (τ (M.op X0 (M.op X0 (σ X1)))) := by
            intro X0 X1
            first
            | (have i₁ := b4e36336 X0 X1
               have i₂ := b4e29609 X0 y X1
               grind)
            | exact superpose b4e29609 b4e36336
            | exact resolve b4e36336 b4e29609
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29609 b4e36336
          have b4e36512 : ∀ X0 X1 : G, (M.op (τ X0) (M.op x (M.op (τ X0) (M.op x X1)))) = (τ (M.op X0 (M.op X0 (σ X1)))) := by
            intro X0 X1
            first
            | (have i₁ := b4e36431 X0 X1
               have i₂ := b4e793 (τ X0) x X1
               grind)
            | exact superpose b4e793 b4e36431
            | exact resolve b4e36431 b4e793
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e793 b4e36431
          have b4e36577 : ∀ X0 X1 : G, (M.op (τ X0) (M.op (τ X0) X1)) = (τ (M.op X0 (M.op X0 (σ X1)))) := by
            intro X0 X1
            first
            | (have i₁ := b4e36512 X0 X1
               have i₂ := b4e847 x (τ X0) (τ X0) X1
               grind)
            | exact superpose b4e847 b4e36512
            | exact resolve b4e36512 b4e847
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e847 b4e36512
          have b4e36634 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) X1) = (τ (M.op X0 (M.op X0 (σ X1)))) := by
            intro X0 X1
            first
            | (have i₁ := b4e36577 X0 X1
               have i₂ := b4e3696 X0 X1
               grind)
            | exact superpose b4e3696 b4e36577
            | exact resolve b4e36577 b4e3696
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3696 b4e36577
          have b4e222807 : ∀ X0 X1 : G, (M.op (M.op X1 (σ y)) (M.op (σ y) X0)) = (M.op X1 (k (σ (σ y)) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 (k (σ (σ y)) X0) (σ y)
               have i₂ := b4e2406 X0
               grind)
            | exact superpose b4e2406 b4e13
            | exact resolve b4e13 b4e2406
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2406
          have b4e222884 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (k (σ (σ y)) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e222807 X0 X1
               have i₂ := b4e13 X1 X0 (σ y)
               grind)
            | exact superpose b4e13 b4e222807
            | exact resolve b4e222807 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e222807
          have b4e227272 : ∀ X0 X1 : G, (k (τ (M.op (M.op X0 X0) (σ y))) X1) = (τ (M.op (M.op (M.op X0 X0) (σ y)) (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e214 (M.op X0 (σ y)) X1
               have i₂ := b4e455 X0 X0
               grind)
            | exact superpose b4e455 b4e214
            | exact resolve b4e214 b4e455
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e455
          have b4e227395 : ∀ X0 X1 : G, (k (τ (M.op (M.op X0 X0) (σ y))) X1) = (τ (M.op (M.op X0 X0) (M.op (σ y) (σ X1)))) := by
            intro X0 X1
            first
            | (have i₁ := b4e227272 X0 X1
               have i₂ := b4e486 (M.op X0 X0) (σ y) (σ X1)
               grind)
            | exact superpose b4e486 b4e227272
            | exact resolve b4e227272 b4e486
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e227272
          have b4e227464 : ∀ X0 X1 : G, (k (τ (M.op (M.op X0 X0) (σ y))) X1) = (τ (M.op X0 (M.op X0 (M.op (σ y) (σ X1))))) := by
            intro X0 X1
            first
            | (have i₁ := b4e227395 X0 X1
               have i₂ := b4e486 X0 X0 (M.op (σ y) (σ X1))
               grind)
            | exact superpose b4e486 b4e227395
            | exact resolve b4e227395 b4e486
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e227395
          have b4e227515 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X0 (σ X1)))) = (k (τ (M.op (M.op X0 X0) (σ y))) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e227464 X0 X1
               have i₂ := b4e234 (σ X1) X0
               grind)
            | exact superpose b4e234 b4e227464
            | exact resolve b4e227464 b4e234
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e234 b4e227464
          have b4e227554 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X0 (σ X1)))) = (k (k (τ (M.op X0 X0)) y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e227515 X0 X1
               have i₂ := b4e214 X0 y
               grind)
            | exact superpose b4e214 b4e227515
            | exact resolve b4e227515 b4e214
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e214 b4e227515
          have b4e227579 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X0 (σ X1)))) = (k (M.op (τ (M.op X0 X0)) y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e227554 X0 X1
               have i₂ := b4e2436 X0 y
               grind)
            | exact superpose b4e2436 b4e227554
            | exact resolve b4e227554 b4e2436
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2436 b4e227554
          have b4e227593 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) X1) = (k (M.op (τ (M.op X0 X0)) y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e227579 X0 X1
               have i₂ := b4e36634 X0 X1
               grind)
            | exact superpose b4e36634 b4e227579
            | exact resolve b4e227579 b4e36634
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36634 b4e227579
          have b4e229267 : ∀ X0 X1 : G, (M.op (σ X1) (k (σ (σ y)) X0)) = (M.op (σ (k X1 x)) (M.op (σ x) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e284 X1 (k (σ (σ y)) X0)
               have i₂ := b4e222884 X0 (σ x)
               grind)
            | exact superpose b4e222884 b4e284
            | exact resolve b4e284 b4e222884
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e284
          have b4e229409 : ∀ X0 X1 : G, (M.op (σ X1) (k (σ (σ y)) X0)) = (M.op (σ (M.op (k X1 x) x)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e229267 X0 X1
               have i₂ := b4e3690 (k X1 x) X0
               grind)
            | exact superpose b4e3690 b4e229267
            | exact resolve b4e229267 b4e3690
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3690 b4e229267
          have b4e229502 : ∀ X0 X1 : G, (M.op (σ X1) (k (σ (σ y)) X0)) = (M.op (σ (M.op (M.op X1 x) x)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e229409 X0 X1
               have i₂ := b4e1261 X1
               grind)
            | exact superpose b4e1261 b4e229409
            | exact resolve b4e229409 b4e1261
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1261 b4e229409
          have b4e229577 : ∀ X0 X1 : G, (M.op (σ X1) (k (σ (σ y)) X0)) = (M.op (σ (M.op X1 (M.op x x))) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e229502 X0 X1
               have i₂ := b4e486 X1 x x
               grind)
            | exact superpose b4e486 b4e229502
            | exact resolve b4e229502 b4e486
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e229502
          have b4e229624 : ∀ X0 X1 : G, (M.op (σ X1) X0) = (M.op (σ (M.op X1 (M.op x x))) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e229577 X0 X1
               have i₂ := b4e222884 X0 (σ X1)
               grind)
            | exact superpose b4e222884 b4e229577
            | exact resolve b4e229577 b4e222884
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e222884 b4e229577
          have b4e286938 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (σ X1))) = (σ (k (M.op (τ (M.op X0 X0)) y) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e11902 X0 (σ X1)
               have i₂ := b4e4354 X0 y X1
               grind)
            | exact superpose b4e4354 b4e11902
            | exact resolve b4e11902 b4e4354
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4354 b4e11902
          have b4e286943 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (σ X1))) = (σ (M.op (τ (M.op X0 X0)) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e286938 X0 X1
               have i₂ := b4e227593 X0 X1
               grind)
            | exact superpose b4e227593 b4e286938
            | exact resolve b4e286938 b4e227593
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e227593 b4e286938
          have b4e318238 : ∀ X0 X1 : G, (M.op (σ (M.op X0 (M.op x x))) X1) = (M.op (σ (M.op X0 y)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e229624 X1 (M.op X0 y)
               have i₂ := b4e100 X0 (M.op x x)
               grind)
            | exact superpose b4e100 b4e229624
            | exact resolve b4e229624 b4e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e100
          have b4e318775 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (M.op X0 y)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e318238 X0 X1
               have i₂ := b4e229624 X1 X0
               grind)
            | exact superpose b4e229624 b4e318238
            | exact resolve b4e318238 b4e229624
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e229624 b4e318238
          have b4e318956 : ∀ X0 : G, (σ (M.op (M.op X0 y) (M.op X0 y))) = (M.op (σ X0) (σ (M.op X0 y))) := by
            intro X0
            first
            | (have i₁ := b4e408 (M.op X0 y)
               have i₂ := b4e318775 X0 (σ (M.op X0 y))
               grind)
            | exact superpose b4e318775 b4e408
            | exact resolve b4e408 b4e318775
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e408 b4e318775
          have b4e319411 : ∀ X0 : G, (σ (M.op X0 (M.op y (M.op X0 y)))) = (M.op (σ X0) (σ (M.op X0 y))) := by
            intro X0
            first
            | (have i₁ := b4e318956 X0
               have i₂ := b4e486 X0 y (M.op X0 y)
               grind)
            | exact superpose b4e486 b4e318956
            | exact resolve b4e318956 b4e486
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e486 b4e318956
          have b4e319481 : ∀ X0 : G, (σ (M.op X0 (M.op X0 y))) = (M.op (σ X0) (σ (M.op X0 y))) := by
            intro X0
            first
            | (have i₁ := b4e319411 X0
               have i₂ := b4e42 (M.op X0 y) X0
               grind)
            | exact superpose b4e42 b4e319411
            | exact resolve b4e319411 b4e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42 b4e319411
          have b4e381895 : ∀ X0 X1 : G, (σ (M.op (τ X0) X1)) = (M.op X0 (M.op X0 (σ (M.op (τ X0) X1)))) := by
            intro X0 X1
            first
            | (have i₁ := b4e286943 X0 (M.op (τ X0) X1)
               have i₂ := b4e2448 X0 X1
               grind)
            | exact superpose b4e2448 b4e286943
            | exact resolve b4e286943 b4e2448
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2448 b4e286943
          have b4e401510 : ∀ X0 : G, (σ (M.op (τ X0) (M.op (τ X0) y))) = (M.op X0 (σ (M.op (τ X0) y))) := by
            intro X0
            first
            | (have i₁ := b4e319481 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e319481
            | exact resolve b4e319481 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e319481
          have b4e401556 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op X0 (σ (M.op (τ X0) y))) := by
            intro X0
            first
            | (have i₁ := b4e401510 X0
               have i₂ := b4e2263 X0 y
               grind)
            | exact superpose b4e2263 b4e401510
            | exact resolve b4e401510 b4e2263
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2263 b4e401510
          have b4e480981 : ∀ X0 : G, (σ (M.op (τ X0) y)) = (M.op X0 (M.op X0 (M.op X0 (σ y)))) := by
            intro X0
            first
            | (have i₁ := b4e381895 X0 y
               have i₂ := b4e401556 X0
               grind)
            | exact superpose b4e401556 b4e381895
            | exact resolve b4e381895 b4e401556
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e381895 b4e401556
          have b4e481018 : ∀ X0 : G, (M.op X0 (σ y)) = (σ (M.op (τ X0) y)) := by
            intro X0
            first
            | (have i₁ := b4e480981 X0
               have i₂ := b4e3732 X0 X0 (σ y)
               grind)
            | exact superpose b4e3732 b4e480981
            | exact resolve b4e480981 b4e3732
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3732 b4e480981
          have b4e481057 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b4e481018 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e481018
            | exact resolve b4e481018 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e481018
          have b4e481519 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e481057 x
               grind)
            | exact superpose b4e481057 b4e20
            | (have r₁ := b4e20
               have r₂ := b4e481057 x
               grind)
            | exact resolve b4e20 b4e481057
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e481057
          have b4e482398 : False := by grind
          exact b4e482398
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op y y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e41 : ∀ X0 : G, y ≠ y ∨ (M.op y X0) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b5e16 y X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e16
            | (have j0 := b5e16 y X0
               grind)
            | (have r₁ := b5e16 y x
               have r₂ := b5e22
               grind)
            | exact resolve b5e16 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e44 : ∀ X0 : G, (M.op y X0) = (k y X0) := by
            intro X0
            first
            | (have j0 := b5e41 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41
          have b5e66 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e18 X0 (σ y)
               grind)
            | exact superpose b5e18 b5e24
            | (have j1 := b5e18 X0 X0
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 (σ y) x
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 X0 (σ y)
               grind)
            | exact resolve b5e24 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e69 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b5e66 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e66
          have b5e77 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b5e69 X0
               have j1 := b5e16 X0 (σ y)
               grind)
            | (have r₁ := b5e69 X0
               have r₂ := b5e16 X0 x
               grind)
            | exact resolve b5e69 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e69
          have b5e84 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 y
               have i₂ := b5e77 (σ X0)
               grind)
            | exact superpose b5e77 b5e19
            | exact resolve b5e19 b5e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e77
          have b5e274 : (σ y) ≠ (σ (k y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e84 y
               grind)
            | exact superpose b5e84 b5e24
            | exact resolve b5e24 b5e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e84
          have b5e289 : (σ y) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e274
               have i₂ := b5e44 y
               grind)
            | exact superpose b5e44 b5e274
            | exact resolve b5e274 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44 b5e274
          have b5e298 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e289
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e289
            | exact resolve b5e289 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e289
          have b5e299 : False := by grind
          exact b5e299
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op x x) := by grind
        have b6e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e33 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b6e15 (σ x) X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e15
          | (have j0 := b6e15 (σ x) X0
             grind)
          | (have r₁ := b6e15 (σ x) x
             have r₂ := b6e22
             grind)
          | exact resolve b6e15 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e36 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have j0 := b6e33 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e33
        have b6e38 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 x X0
             have i₂ := b6e36 (σ X0)
             grind)
          | exact superpose b6e36 b6e18
          | exact resolve b6e18 b6e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36
        have b6e96 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e38 x
             grind)
          | exact superpose b6e38 b6e22
          | exact resolve b6e22 b6e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38
        have b6e132 : (τ (σ x)) = (k x x) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e96
             grind)
          | exact superpose b6e96 b6e13
          | exact resolve b6e13 b6e96
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e96
        have b6e134 : x = (k x x) := by
          first
          | (have i₁ := b6e132
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e132
          | exact resolve b6e132 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e132
        have b6e152 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e134
             grind)
          | exact superpose b6e134 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e134
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e134
        have b6e153 : x = (M.op x x) := by grind
        clear b6e152
        have b6e155 : False := by grind
        exact b6e155
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op y y) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e43 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) X0) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e16 (σ y) X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | (have j0 := b7e16 (σ y) X0
               grind)
            | (have r₁ := b7e16 (σ y) x
               have r₂ := b7e24
               grind)
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e46 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) := by
            intro X0
            first
            | (have j0 := b7e43 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e43
          have b7e48 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 y X0
               have i₂ := b7e46 (σ X0)
               grind)
            | exact superpose b7e46 b7e19
            | exact resolve b7e19 b7e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e147 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e48 y
               grind)
            | exact superpose b7e48 b7e24
            | exact resolve b7e24 b7e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e173 : (τ (σ y)) = (k y y) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e147
               grind)
            | exact superpose b7e147 b7e14
            | exact resolve b7e14 b7e147
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e147
          have b7e175 : y = (k y y) := by
            first
            | (have i₁ := b7e173
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e173
            | exact resolve b7e173 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e173
          have b7e192 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e18 y y
               have i₂ := b7e175
               grind)
            | exact superpose b7e175 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e175
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e175
          have b7e193 : y = (M.op y y) := by grind
          clear b7e192
          have b7e195 : False := by grind
          exact b7e195
        · have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op x x) := by grind
          have b8e22 : y ≠ (M.op y y) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e77 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 X0 (σ y)
               grind)
            | exact superpose b8e18 b8e24
            | (have j1 := b8e18 X0 X0
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ y) x
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 X0 (σ y)
               grind)
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e83 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b8e77 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e77
          have b8e91 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b8e83 X0
               have j1 := b8e16 X0 (σ y)
               grind)
            | (have r₁ := b8e83 X0
               have r₂ := b8e16 X0 x
               grind)
            | exact resolve b8e83 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e83
          have b8e98 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 y
               have i₂ := b8e91 (σ X0)
               grind)
            | exact superpose b8e91 b8e19
            | exact resolve b8e19 b8e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e91
          have b8e116 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e98 x
               grind)
            | exact superpose b8e98 b8e20
            | exact resolve b8e20 b8e98
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e98
          have b8e173 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b8e116
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e116
            | (have j1 := b8e18 x x
               grind)
            | exact resolve b8e116 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e116
          have b8e174 : x = (M.op x x) ∨ y = (M.op y y) := by grind
          clear b8e173
          have b8e175 : y = (M.op y y) := by
            first
            | (have r₁ := b8e174
               have r₂ := b8e21
               grind)
            | exact resolve b8e174 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e174
          have b8e176 : False := by grind
          exact b8e176

/-- `Equation3875`: `x ◇ x = (x ◇ (y ◇ z)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxy_y_pyx_pyx_pxy_Equation3875 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3875 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3875.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (M.op y y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op x x) = (M.op y y) := by grind
      have b0e20 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e43 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e14 (σ y) X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have j0 := b0e14 X0 (σ x)
           grind)
        | (have r₁ := b0e14 (σ x) (σ y)
           have r₂ := b0e20
           grind)
        | (have r₁ := b0e14 (σ y) (σ x)
           have r₂ := b0e20
           grind)
        | exact resolve b0e14 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e44 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e14 y X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 X0 x
           grind)
        | (have r₁ := b0e14 x y
           have r₂ := b0e19
           grind)
        | (have r₁ := b0e14 y x
           have r₂ := b0e19
           grind)
        | exact resolve b0e14 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e216 : (M.op x y) = (k y x) := by
        first
        | (have j0 := b0e44 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44
      have b0e556 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have j0 := b0e43 (σ x)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43
      have b0e558 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
        first
        | (have i₁ := b0e556
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e556
        | exact resolve b0e556 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e556
      have b0e568 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e558
           have i₂ := b0e216
           grind)
        | exact superpose b0e216 b0e558
        | exact resolve b0e558 b0e216
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e216 b0e558
      have b0e572 : False := by grind
      exact b0e572
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X1 X2)) X2) := by
          intro X0 X1 X2
          grind
        have b1e21 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e33 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (σ y)) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e12 X0 (σ x) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e221 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e33 (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e33
          | exact resolve b1e33 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33
        have b1e241 : False := by grind
        exact b1e241
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op x x) = (M.op y y) := by grind
        have b2e21 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e55 (σ X0)
             grind)
          | exact superpose b2e55 b2e18
          | exact resolve b2e18 b2e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e64 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e57 X0
             have i₂ := b2e55 X0
             grind)
          | exact superpose b2e55 b2e57
          | exact resolve b2e57 b2e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55 b2e57
        have b2e130 : (M.op (σ y) (σ y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e64 x
             grind)
          | exact superpose b2e64 b2e21
          | exact resolve b2e21 b2e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e137 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e130
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e130
          | exact resolve b2e130 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e130
        have b2e138 : False := by grind
        exact b2e138
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X1 X2)) X2) := by
          intro X0 X1 X2
          grind
        have b3e20 : (M.op x x) ≠ (M.op y y) := by grind
        have b3e21 : y = (M.op x y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e31 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 y) y) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 x y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e37 : (M.op x x) = (M.op y y) := by
          first
          | (have i₁ := b3e31 x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e31
          | exact resolve b3e31 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31
        have b3e43 : False := by grind
        exact b3e43
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X1 X2)) X2) := by
            intro X0 X1 X2
            grind
          have b5e21 : (M.op x x) ≠ (M.op y y) := by grind
          have b5e22 : y = (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e33 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 y) y) := by
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
          have b5e39 : (M.op x x) = (M.op y y) := by
            first
            | (have i₁ := b5e33 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e33
            | exact resolve b5e33 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e45 : False := by grind
          exact b5e45
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x x) ≠ (M.op y y) := by grind
        have b6e22 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 X0
             have i₂ := b6e55 (σ X0)
             grind)
          | exact superpose b6e55 b6e18
          | exact resolve b6e18 b6e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e64 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e57 X0
             have i₂ := b6e55 X0
             grind)
          | exact superpose b6e55 b6e57
          | exact resolve b6e57 b6e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55 b6e57
        have b6e133 : (M.op (σ y) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e64 x
             grind)
          | exact superpose b6e64 b6e22
          | exact resolve b6e22 b6e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e140 : (σ (M.op y y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e133
             have i₂ := b6e64 y
             grind)
          | exact superpose b6e64 b6e133
          | exact resolve b6e133 b6e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64 b6e133
        have b6e310 : (M.op x x) = (τ (σ (M.op y y))) := by
          first
          | (have i₁ := b6e13 (M.op x x)
             have i₂ := b6e140
             grind)
          | exact superpose b6e140 b6e13
          | exact resolve b6e13 b6e140
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e140
        have b6e311 : (M.op x x) = (M.op y y) := by
          first
          | (have i₁ := b6e310
             have i₂ := b6e13 (M.op y y)
             grind)
          | exact superpose b6e13 b6e310
          | exact resolve b6e310 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e310
        have b6e317 : False := by grind
        exact b6e317
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X1 X2)) X2) := by
            intro X0 X1 X2
            grind
          have b7e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e29 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (σ y)) (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e117 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e29 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e29
            | exact resolve b7e29 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29
          have b7e131 : False := by grind
          exact b7e131
        · have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : (M.op x x) ≠ (M.op y y) := by grind
          have b8e22 : y ≠ (M.op x y) := by grind
          have b8e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e46 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e48 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e46 (σ X0)
               grind)
            | exact superpose b8e46 b8e19
            | exact resolve b8e19 b8e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e53 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e48 X0
               have i₂ := b8e46 X0
               grind)
            | exact superpose b8e46 b8e48
            | exact resolve b8e48 b8e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e46 b8e48
          have b8e78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b8e88 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op y y) ∨ (k x X0) = (M.op x X0) ∨ (M.op x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e21
               have i₂ := b8e18 x X0
               grind)
            | (have i₁ := b8e21
               have i₂ := b8e18 X0 x
               grind)
            | exact superpose b8e18 b8e21
            | (have j1 := b8e18 x X0
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e18 x y
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e18 y x
               grind)
            | exact resolve b8e21 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e99 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e78 X0 X1
               have i₂ := b8e53 X1
               grind)
            | exact superpose b8e53 b8e78
            | (have j0 := b8e78 X0 X1
               grind)
            | exact resolve b8e78 b8e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e78
          have b8e101 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e99 X0 X1
               have i₂ := b8e53 X0
               grind)
            | exact superpose b8e53 b8e99
            | (have j0 := b8e99 X0 X1
               grind)
            | exact resolve b8e99 b8e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e99
          have b8e279 : (M.op (σ y) (σ y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e53 x
               grind)
            | exact superpose b8e53 b8e23
            | exact resolve b8e23 b8e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e291 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e279
               have i₂ := b8e53 y
               grind)
            | exact superpose b8e53 b8e279
            | exact resolve b8e279 b8e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e53 b8e279
          have b8e546 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
            first
            | (have j0 := b8e88 y
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e88
          have b8e547 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b8e546
               have r₂ := b8e22
               grind)
            | exact resolve b8e546 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e546
          have b8e3819 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e101 x y
               grind)
            | exact superpose b8e101 b8e20
            | (have j1 := b8e101 y x
               grind)
            | exact resolve b8e20 b8e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e101
          have b8e3902 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e3819
               have r₂ := b8e291
               grind)
            | exact resolve b8e3819 b8e291
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e291 b8e3819
          have b8e3949 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e3902
               have r₂ := b8e24
               grind)
            | exact resolve b8e3902 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3902
          have b8e3978 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b8e3949
               have i₂ := b8e547
               grind)
            | exact superpose b8e547 b8e3949
            | exact resolve b8e3949 b8e547
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e547 b8e3949
          have b8e3979 : False := by grind
          exact b8e3979

/-- `Equation4297`: `x ◇ (x ◇ y) = y ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_y_pxy_x_pxy_Equation4297 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4297 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4297.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x y) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
    · have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op x y) := by grind
      have b0e20 : (σ x) = (M.op (σ x) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e22 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e18
        | exact resolve b0e18 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e23 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e22
        | exact resolve b0e22 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22
      have b0e24 : False := by grind
      exact b0e24
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (M.op X2 X2)) := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op x y) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 (τ X0) X1
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e18
          | exact resolve b1e18 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
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
        have b1e31 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e12 (σ x) (σ x) X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) (M.op X3 X3)) = (M.op X2 (M.op X0 (M.op X1 X1))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X2 (M.op X2 X0) X3
             have i₂ := b1e12 X2 X0 X1
             grind)
          | (have i₁ := b1e12 X1 (M.op X2 X2) X2
             have i₂ := b1e12 X0 X1 X2
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op X1 (M.op X0 (M.op X0 X1))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X1 (M.op X2 X2) X3
             have i₂ := b1e12 X0 X1 X2
             grind)
          | (have i₁ := b1e12 X0 (M.op X0 X1) X2
             have i₂ := b1e12 X0 X1 X2
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e36 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 X1 (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e40 : ∀ X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op X1 (M.op X1 (σ y))) := by
          intro X1 X2 X3
          first
          | (have i₁ := b1e33 x X1 X2 X3
             have i₂ := b1e36 x X1
             grind)
          | exact superpose b1e36 b1e33
          | exact resolve b1e33 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33
        have b1e41 : ∀ X2 X3 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op (σ y) (σ y)) := by
          intro X2 X3
          first
          | (have i₁ := b1e40 x X2 X3
             have i₂ := b1e36 x (σ y)
             grind)
          | exact superpose b1e36 b1e40
          | exact resolve b1e40 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40
        have b1e47 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
        have b1e51 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b1e15 (σ x) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e56 : (σ x) ≠ (σ y) ∨ (σ y) = (σ (k x x)) := by
          first
          | (have i₁ := b1e51
             have i₂ := b1e18 x x
             grind)
          | exact superpose b1e18 b1e51
          | exact resolve b1e51 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51
        have b1e60 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (M.op (τ X0) (τ X0))) := by
          intro X0
          grind
        clear b1e25
        have b1e61 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (M.op (τ X0) (τ X0))) := by
          intro X0
          first
          | (have i₁ := b1e60 X0
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e60
          | (have j0 := b1e60 X0
             grind)
          | exact resolve b1e60 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60
        have b1e64 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e61 X0
             have i₂ := b1e36 (τ X0) (τ X0)
             grind)
          | exact superpose b1e36 b1e61
          | (have j0 := b1e61 X0
             grind)
          | exact resolve b1e61 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61
        have b1e68 : (M.op y (σ y)) = (M.op x x) := by
          first
          | (have i₁ := b1e36 x y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e36
          | exact resolve b1e36 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e69 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (σ y)) = (M.op X1 (M.op X0 (σ y))) := by
          intro X0 X1
          first
          | (have i₁ := b1e36 X1 (M.op X1 X0)
             have i₂ := b1e36 X1 X0
             grind)
          | exact superpose b1e36 b1e36
          | exact resolve b1e36 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e74 : ∀ X0 X2 : G, (M.op X0 (σ y)) = (M.op X0 (M.op X2 X2)) := by
          intro X0 X2
          first
          | (have i₁ := b1e12 x X0 X2
             have i₂ := b1e36 x X0
             grind)
          | exact superpose b1e36 b1e12
          | exact resolve b1e12 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b1e90 : ∀ X0 : G, (σ y) = X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e22
             have i₂ := b1e17 (σ x) X0
             grind)
          | (have i₁ := b1e22
             have i₂ := b1e17 X0 (M.op (σ x) (σ x))
             grind)
          | exact superpose b1e17 b1e22
          | (have j1 := b1e17 (σ x) X0
             grind)
          | exact resolve b1e22 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e91 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X1 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e36 X1 X1
             have i₂ := b1e17 X1 X0
             grind)
          | (have i₁ := b1e36 X0 X1
             have i₂ := b1e17 X0 (M.op X0 X1)
             grind)
          | exact superpose b1e17 b1e36
          | (have j1 := b1e17 X1 X0
             grind)
          | exact resolve b1e36 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e95 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b1e97 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e95 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e95
        have b1e101 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b1e97 X0 X1
             have j1 := b1e15 X1 X0
             grind)
          | (have r₁ := b1e97 X1 X0
             have r₂ := b1e15 X0 X1
             grind)
          | exact resolve b1e97 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e97
        have b1e105 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e91 X0 X1
             have j1 := b1e15 X1 X0
             grind)
          | (have r₁ := b1e91 X1 X0
             have r₂ := b1e15 X0 X1
             grind)
          | exact resolve b1e91 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e91
        have b1e106 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ y) = X0 := by
          intro X0
          first
          | (have j0 := b1e90 X0
             have j1 := b1e15 (σ x) X0
             grind)
          | (have r₁ := b1e90 (M.op (σ y) x)
             have r₂ := b1e15 (σ y) x
             grind)
          | (have r₁ := b1e90 x
             have r₂ := b1e15 (σ x) x
             grind)
          | exact resolve b1e90 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e90
        have b1e119 : (M.op (σ y) (σ y)) = (M.op y (M.op x x)) := by
          first
          | (have i₁ := b1e36 y (σ y)
             have i₂ := b1e68
             grind)
          | exact superpose b1e68 b1e36
          | exact resolve b1e36 b1e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e121 : (M.op (σ y) (σ y)) = (M.op y (σ y)) := by
          first
          | (have i₁ := b1e119
             have i₂ := b1e74 y x
             grind)
          | exact superpose b1e74 b1e119
          | exact resolve b1e119 b1e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e119
        have b1e122 : (M.op (σ y) (σ y)) = (M.op x x) := by
          first
          | (have i₁ := b1e121
             have i₂ := b1e68
             grind)
          | exact superpose b1e68 b1e121
          | exact resolve b1e121 b1e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e68 b1e121
        have b1e247 : (σ y) ≠ (M.op x x) ∨ (M.op x x) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b1e15 (σ y) (σ y)
             have i₂ := b1e122
             grind)
          | exact superpose b1e122 b1e15
          | exact resolve b1e15 b1e122
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e256 : (M.op x x) = (σ (k y y)) ∨ (σ y) ≠ (M.op x x) := by
          first
          | (have i₁ := b1e247
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e247
          | exact resolve b1e247 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e247
        have b1e536 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e101 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e101
        have b1e543 : ∀ X0 X1 : G, (M.op X0 (σ y)) ≠ X0 ∨ (k X0 (M.op X1 X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e536 X0 (M.op X1 X1)
             have i₂ := b1e74 X0 X1
             grind)
          | exact superpose b1e74 b1e536
          | (have j0 := b1e536 X0 (σ y)
             grind)
          | exact resolve b1e536 b1e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e604 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (σ y) (σ y))) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op (σ y) (σ y))) := by
          intro X0
          grind
        have b1e609 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (σ y) (σ y))) := by
          intro X0
          first
          | (have j0 := b1e604 X0
             have j1 := b1e536 (M.op X0 X0) (M.op (σ y) (σ y))
             grind)
          | (have r₁ := b1e604 X0
             have r₂ := b1e536 (M.op X0 X0) (M.op (σ y) (σ y))
             grind)
          | exact resolve b1e604 b1e536
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e536 b1e604
        have b1e641 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op x x)) := by
          intro X0
          first
          | (have i₁ := b1e609 X0
             have i₂ := b1e122
             grind)
          | exact superpose b1e122 b1e609
          | exact resolve b1e609 b1e122
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e609
        have b1e716 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ y) := by
          intro X0
          first
          | (have i₁ := b1e18 x X0
             have i₂ := b1e106 (σ X0)
             grind)
          | exact superpose b1e106 b1e18
          | (have j1 := b1e106 (σ X0)
             grind)
          | exact resolve b1e18 b1e106
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e106
        have b1e849 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (σ y)) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 (M.op X2 X2)))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e36 (M.op X0 X1) (M.op X3 X3)
             have i₂ := b1e32 X1 X2 X0 X3
             grind)
          | exact superpose b1e32 b1e36
          | exact resolve b1e36 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32
        have b1e927 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X3) (σ y)) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 (σ y)))) := by
          intro X0 X1 X3
          first
          | (have i₁ := b1e849 X0 X1 x X3
             have i₂ := b1e74 X1 x
             grind)
          | exact superpose b1e74 b1e849
          | exact resolve b1e849 b1e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e849
        have b1e1033 : ∀ X0 X1 X3 : G, (M.op X3 (M.op X3 (σ y))) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 (σ y)))) := by
          intro X0 X1 X3
          first
          | (have i₁ := b1e927 X0 X1 X3
             have i₂ := b1e69 X3 X3
             grind)
          | exact superpose b1e69 b1e927
          | exact resolve b1e927 b1e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e927
        have b1e1132 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 (σ y)))) := by
          intro X0 X1
          first
          | (have i₁ := b1e1033 X0 X1 x
             have i₂ := b1e36 x (σ y)
             grind)
          | exact superpose b1e36 b1e1033
          | exact resolve b1e1033 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1033
        have b1e1200 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 (σ y)))) := by
          intro X0 X1
          first
          | (have i₁ := b1e1132 X0 X1
             have i₂ := b1e122
             grind)
          | exact superpose b1e122 b1e1132
          | exact resolve b1e1132 b1e122
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1132
        have b1e2822 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e87 x x
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e87
          | exact resolve b1e87 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2823 : (M.op x x) = (σ (k y y)) ∨ (σ y) = (M.op x x) ∨ (σ y) = (M.op x x) := by
          first
          | (have i₁ := b1e87 y y
             have i₂ := b1e122
             grind)
          | exact superpose b1e122 b1e87
          | exact resolve b1e87 b1e122
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e87
        have b1e2941 : (M.op x x) = (σ (k y y)) ∨ (σ y) = (M.op x x) := by grind
        clear b1e2823
        have b1e2942 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b1e2822
        have b1e2991 : (M.op x x) = (σ (k y y)) := by
          first
          | (have r₁ := b1e2941
             have r₂ := b1e256
             grind)
          | exact resolve b1e2941 b1e256
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e256 b1e2941
        have b1e2992 : (σ y) = (σ (k x x)) := by
          first
          | (have r₁ := b1e2942
             have r₂ := b1e56
             grind)
          | exact resolve b1e2942 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56 b1e2942
        have b1e3037 : (k x x) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (k x x)
             have i₂ := b1e2992
             grind)
          | exact superpose b1e2992 b1e13
          | exact resolve b1e13 b1e2992
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2992
        have b1e3052 : y = (k x x) := by
          first
          | (have i₁ := b1e3037
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e3037
          | exact resolve b1e3037 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3037
        have b1e3403 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e17 x x
             have i₂ := b1e3052
             grind)
          | exact superpose b1e3052 b1e17
          | (have j0 := b1e17 x x
             grind)
          | exact resolve b1e17 b1e3052
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e3404 : y = (M.op x x) ∨ x = (M.op x x) := by grind
        clear b1e3403
        have b1e3700 : (k y y) = (τ (M.op x x)) := by
          first
          | (have i₁ := b1e13 (k y y)
             have i₂ := b1e2991
             grind)
          | exact superpose b1e2991 b1e13
          | exact resolve b1e13 b1e2991
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e5613 : y = (k y y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e641 x
             have i₂ := b1e3404
             grind)
          | exact superpose b1e3404 b1e641
          | exact resolve b1e641 b1e3404
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e641
        have b1e5970 : (σ y) = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e2991
             have i₂ := b1e5613
             grind)
          | exact superpose b1e5613 b1e2991
          | exact resolve b1e2991 b1e5613
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5613
        have b1e6026 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op (τ (σ X0)) (τ (σ X0)))))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e47 X0 (σ (M.op (τ (σ X0)) (τ (σ X0))))
             have i₂ := b1e64 (σ X0)
             grind)
          | exact superpose b1e64 b1e47
          | (have j1 := b1e64 (σ X0)
             grind)
          | exact resolve b1e47 b1e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e64
        have b1e6037 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e6026 X0
             have i₂ := b1e13 (M.op (τ (σ X0)) (τ (σ X0)))
             grind)
          | exact superpose b1e13 b1e6026
          | (have j0 := b1e6026 X0
             grind)
          | exact resolve b1e6026 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6026
        have b1e6061 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e6037 X0
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e6037
          | (have j0 := b1e6037 X0
             grind)
          | exact resolve b1e6037 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6037
        have b1e6074 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e6061 X0
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e6061
          | (have j0 := b1e6061 X0
             grind)
          | exact resolve b1e6061 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6061
        have b1e6080 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have j0 := b1e6074 X0
             have j1 := b1e543 X0 X0
             grind)
          | (have r₁ := b1e6074 X0
             have r₂ := b1e543 X0 x
             grind)
          | exact resolve b1e6074 b1e543
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e543 b1e6074
        have b1e6132 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          first
          | (have i₁ := b1e47 X0 (M.op (σ X0) (σ X0))
             have i₂ := b1e6080 (σ X0)
             grind)
          | exact superpose b1e6080 b1e47
          | exact resolve b1e47 b1e6080
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e6137 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e6132 X0
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e6132
          | exact resolve b1e6132 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6132
        have b1e6556 : (k y y) = (k (k y y) (τ (M.op (M.op x x) (M.op x x)))) := by
          first
          | (have i₁ := b1e6137 (k y y)
             have i₂ := b1e2991
             grind)
          | exact superpose b1e2991 b1e6137
          | exact resolve b1e6137 b1e2991
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6137
        have b1e6618 : (k y y) = (k (k y y) (τ (M.op (M.op x x) (σ y)))) := by
          first
          | (have i₁ := b1e6556
             have i₂ := b1e74 (M.op x x) x
             grind)
          | exact superpose b1e74 b1e6556
          | exact resolve b1e6556 b1e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6556
        have b1e6626 : (k y y) = (k (k y y) (τ (M.op x (M.op x (σ y))))) := by
          first
          | (have i₁ := b1e6618
             have i₂ := b1e69 x x
             grind)
          | exact superpose b1e69 b1e6618
          | exact resolve b1e6618 b1e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e69 b1e6618
        have b1e6631 : (k y y) = (k (k y y) (τ (M.op (σ y) (σ y)))) := by
          first
          | (have i₁ := b1e6626
             have i₂ := b1e36 x (σ y)
             grind)
          | exact superpose b1e36 b1e6626
          | exact resolve b1e6626 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6626
        have b1e6635 : (k y y) = (k (k y y) (τ (M.op x x))) := by
          first
          | (have i₁ := b1e6631
             have i₂ := b1e122
             grind)
          | exact superpose b1e122 b1e6631
          | exact resolve b1e6631 b1e122
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6631
        have b1e6639 : (k y y) = (k (k y y) (k y y)) := by
          first
          | (have i₁ := b1e6635
             have i₂ := b1e3700
             grind)
          | exact superpose b1e3700 b1e6635
          | exact resolve b1e6635 b1e3700
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3700 b1e6635
        have b1e21151 : (k y y) = (M.op (k y y) (k y y)) ∨ (k y y) = (M.op (k y y) (k y y)) ∨ (k y y) = (M.op (k y y) (k y y)) := by
          first
          | (have i₁ := b1e17 (k y y) (k y y)
             have i₂ := b1e6639
             grind)
          | exact superpose b1e6639 b1e17
          | (have j0 := b1e17 (k y y) (k y y)
             grind)
          | exact resolve b1e17 b1e6639
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6639
        have b1e21170 : (k y y) = (M.op (k y y) (k y y)) := by grind
        clear b1e21151
        have b1e25489 : y = (σ y) ∨ x = (σ y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e3404
             have i₂ := b1e5970
             grind)
          | exact superpose b1e5970 b1e3404
          | exact resolve b1e3404 b1e5970
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3404
        have b1e25536 : x ≠ (σ y) ∨ x = (M.op x x) := by grind
        clear b1e5970
        have b1e25555 : x = (M.op x x) ∨ y = (σ y) := by
          first
          | (have r₁ := b1e25489
             have r₂ := b1e25536
             grind)
          | exact resolve b1e25489 b1e25536
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25489 b1e25536
        have b1e32563 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (k y y) (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e41 (k y y) X0
             have i₂ := b1e21170
             grind)
          | exact superpose b1e21170 b1e41
          | exact resolve b1e41 b1e21170
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41
        have b1e32589 : (M.op (k y y) (σ y)) = (M.op (k y y) (k y y)) := by
          first
          | (have i₁ := b1e36 (k y y) (k y y)
             have i₂ := b1e21170
             grind)
          | exact superpose b1e21170 b1e36
          | exact resolve b1e36 b1e21170
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e32623 : (k y y) = (M.op (k y y) (σ y)) := by
          first
          | (have i₁ := b1e32589
             have i₂ := b1e21170
             grind)
          | exact superpose b1e21170 b1e32589
          | exact resolve b1e32589 b1e21170
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e21170 b1e32589
        have b1e32632 : (M.op (σ y) (σ y)) = (M.op (k y y) (σ y)) := by
          first
          | (have i₁ := b1e32563 x
             have i₂ := b1e74 (k y y) x
             grind)
          | exact superpose b1e74 b1e32563
          | exact resolve b1e32563 b1e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e74 b1e32563
        have b1e32661 : (M.op (σ y) (σ y)) = (k y y) := by
          first
          | (have i₁ := b1e32632
             have i₂ := b1e32623
             grind)
          | exact superpose b1e32623 b1e32632
          | exact resolve b1e32632 b1e32623
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32623 b1e32632
        have b1e32676 : (M.op x x) = (k y y) := by
          first
          | (have i₁ := b1e32661
             have i₂ := b1e122
             grind)
          | exact superpose b1e122 b1e32661
          | exact resolve b1e32661 b1e122
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e122 b1e32661
        have b1e33364 : (M.op x x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e2991
             have i₂ := b1e32676
             grind)
          | exact superpose b1e32676 b1e2991
          | exact resolve b1e2991 b1e32676
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2991 b1e32676
        have b1e35669 : (M.op (σ x) (M.op x x)) = (σ (k x (M.op x x))) ∨ (σ y) = (M.op x x) := by
          first
          | (have i₁ := b1e716 (M.op x x)
             have i₂ := b1e33364
             grind)
          | exact superpose b1e33364 b1e716
          | exact resolve b1e716 b1e33364
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e716 b1e33364
        have b1e35741 : (σ x) = (M.op (σ x) (M.op x x)) ∨ (σ y) = (M.op x x) := by
          first
          | (have i₁ := b1e35669
             have i₂ := b1e6080 x
             grind)
          | exact superpose b1e6080 b1e35669
          | exact resolve b1e35669 b1e6080
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e6080 b1e35669
        have b1e35772 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op x x) := by
          first
          | (have i₁ := b1e35741
             have i₂ := b1e31 x
             grind)
          | exact superpose b1e31 b1e35741
          | exact resolve b1e35741 b1e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31 b1e35741
        have b1e35790 : (σ y) = (M.op x x) := by
          first
          | (have r₁ := b1e35772
             have r₂ := b1e21
             grind)
          | exact resolve b1e35772 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35772
        have b1e35919 : y = (σ y) ∨ x = (σ y) := by
          first
          | (have i₁ := b1e25555
             have i₂ := b1e35790
             grind)
          | exact superpose b1e35790 b1e25555
          | exact resolve b1e25555 b1e35790
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25555
        have b1e35948 : x ≠ (σ y) ∨ (σ y) = (k x x) := by
          first
          | (have i₁ := b1e15 x x
             have i₂ := b1e35790
             grind)
          | exact superpose b1e35790 b1e15
          | exact resolve b1e15 b1e35790
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e35956 : (σ y) = (M.op (σ y) (M.op x (M.op x (σ y)))) := by
          first
          | (have i₁ := b1e1200 x x
             have i₂ := b1e35790
             grind)
          | exact superpose b1e35790 b1e1200
          | exact resolve b1e1200 b1e35790
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1200 b1e35790
        have b1e35969 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) := by
          first
          | (have i₁ := b1e35956
             have i₂ := b1e36 x (σ y)
             grind)
          | exact superpose b1e36 b1e35956
          | exact resolve b1e35956 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35956
        have b1e35973 : y = (σ y) ∨ x ≠ (σ y) := by
          first
          | (have i₁ := b1e35948
             have i₂ := b1e3052
             grind)
          | exact superpose b1e3052 b1e35948
          | exact resolve b1e35948 b1e3052
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3052 b1e35948
        have b1e35986 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e35969
             have i₂ := b1e36 (σ y) (σ y)
             grind)
          | exact superpose b1e36 b1e35969
          | exact resolve b1e35969 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35969
        have b1e35988 : y = (σ y) := by
          first
          | (have r₁ := b1e35973
             have r₂ := b1e35919
             grind)
          | exact resolve b1e35973 b1e35919
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35919 b1e35973
        have b1e37934 : (σ x) ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e35988
             grind)
          | exact superpose b1e35988 b1e21
          | exact resolve b1e21 b1e35988
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e38012 : ∀ X0 : G, (σ (k y X0)) = (k y (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 y X0
             have i₂ := b1e35988
             grind)
          | exact superpose b1e35988 b1e18
          | exact resolve b1e18 b1e35988
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e68377 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ (M.op (σ y) X0) = (k (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b1e105 X0 (σ y)
             have i₂ := b1e35986
             grind)
          | exact superpose b1e35986 b1e105
          | (have j0 := b1e105 X0 (σ y)
             grind)
          | exact resolve b1e105 b1e35986
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e105 b1e35986
        have b1e68492 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) := by
          intro X0
          first
          | (have j0 := b1e68377 X0
             have j1 := b1e15 (σ y) X0
             grind)
          | (have r₁ := b1e68377 x
             have r₂ := b1e15 (σ y) x
             grind)
          | exact resolve b1e68377 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e68377
        have b1e68531 : ∀ X0 : G, (M.op y X0) = (k y X0) := by
          intro X0
          first
          | (have i₁ := b1e68492 X0
             have i₂ := b1e35988
             grind)
          | exact superpose b1e35988 b1e68492
          | exact resolve b1e68492 b1e35988
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e68492
        have b1e74727 : ∀ X0 : G, (σ (k y X0)) = (M.op y (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e68531 (σ X0)
             have i₂ := b1e38012 X0
             grind)
          | exact superpose b1e38012 b1e68531
          | exact resolve b1e68531 b1e38012
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38012
        have b1e74772 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b1e74727 X0
             have i₂ := b1e68531 X0
             grind)
          | exact superpose b1e68531 b1e74727
          | exact resolve b1e74727 b1e68531
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e68531 b1e74727
        have b1e83452 : ∀ X0 : G, (σ (M.op X0 (σ y))) = (M.op y (σ (M.op y X0))) := by
          intro X0
          first
          | (have i₁ := b1e74772 (M.op y X0)
             have i₂ := b1e36 y X0
             grind)
          | exact superpose b1e36 b1e74772
          | exact resolve b1e74772 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e83726 : ∀ X0 : G, (σ (M.op X0 (σ y))) = (M.op y (M.op y (σ X0))) := by
          intro X0
          first
          | (have i₁ := b1e83452 X0
             have i₂ := b1e74772 X0
             grind)
          | exact superpose b1e74772 b1e83452
          | exact resolve b1e83452 b1e74772
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e74772 b1e83452
        have b1e83812 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 (σ y))) := by
          intro X0
          first
          | (have i₁ := b1e83726 X0
             have i₂ := b1e36 y (σ X0)
             grind)
          | exact superpose b1e36 b1e83726
          | exact resolve b1e83726 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e36 b1e83726
        have b1e83845 : ∀ X0 : G, (M.op (σ X0) y) = (σ (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b1e83812 X0
             have i₂ := b1e35988
             grind)
          | exact superpose b1e35988 b1e83812
          | exact resolve b1e83812 b1e35988
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35988 b1e83812
        have b1e86456 : (σ x) = (M.op (σ x) y) := by
          first
          | (have i₁ := b1e83845 x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e83845
          | exact resolve b1e83845 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e83845
        have b1e86707 : False := by grind
        exact b1e86707
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op x y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e46 : x ≠ x ∨ x = (k x y) := by
          first
          | (have i₁ := b2e15 x y
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
        have b2e49 : x = (k x y) := by grind
        clear b2e46
        have b2e70 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e22
             have i₂ := b2e17 (σ x) X0
             grind)
          | (have i₁ := b2e22
             have i₂ := b2e17 X0 (M.op (σ x) (σ x))
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
        have b2e84 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have j0 := b2e70 X0
             have j1 := b2e15 (σ x) X0
             grind)
          | (have r₁ := b2e70 x
             have r₂ := b2e15 (σ x) x
             grind)
          | exact resolve b2e70 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e70
        have b2e245 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e84 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e84
        have b2e246 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e245
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e245
          | exact resolve b2e245 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e245
        have b2e247 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e246
             have i₂ := b2e49
             grind)
          | exact superpose b2e49 b2e246
          | exact resolve b2e246 b2e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e49 b2e246
        have b2e248 : False := by grind
        exact b2e248
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (M.op X2 X2)) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : x ≠ (M.op x y) := by grind
        have b3e21 : y = (M.op x x) := by grind
        have b3e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e24 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e19
          | exact resolve b3e19 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e18 (τ X0) X1
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e18
          | exact resolve b3e18 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b3e28 : ∀ X0 : G, (M.op (σ y) (M.op X0 X0)) = (M.op (σ x) (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ x) (σ y) X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) (M.op X3 X3)) = (M.op X2 (M.op X0 (M.op X1 X1))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 X2 (M.op X2 X0) X3
             have i₂ := b3e12 X2 X0 X1
             grind)
          | (have i₁ := b3e12 X1 (M.op X2 X2) X2
             have i₂ := b3e12 X0 X1 X2
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op X1 (M.op X0 (M.op X0 X1))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 X1 (M.op X2 X2) X3
             have i₂ := b3e12 X0 X1 X2
             grind)
          | (have i₁ := b3e12 X0 (M.op X0 X1) X2
             have i₂ := b3e12 X0 X1 X2
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e33 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 y) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 X1 x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e37 : ∀ X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op X1 (M.op X1 y)) := by
          intro X1 X2 X3
          first
          | (have i₁ := b3e30 x X1 X2 X3
             have i₂ := b3e33 x X1
             grind)
          | exact superpose b3e33 b3e30
          | exact resolve b3e30 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30
        have b3e38 : ∀ X2 X3 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op y y) := by
          intro X2 X3
          first
          | (have i₁ := b3e37 x X2 X3
             have i₂ := b3e33 x y
             grind)
          | exact superpose b3e33 b3e37
          | exact resolve b3e37 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37
        have b3e45 : x ≠ y ∨ y = (k x x) := by
          first
          | (have i₁ := b3e15 x x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e15
          | exact resolve b3e15 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e47 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b3e15 (σ x) (σ y)
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
        have b3e50 : (σ x) = (k (σ x) (σ y)) := by grind
        clear b3e47
        have b3e52 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b3e50
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e50
          | exact resolve b3e50 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50
        have b3e56 : (k x y) = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 (k x y)
             have i₂ := b3e52
             grind)
          | exact superpose b3e52 b3e13
          | exact resolve b3e13 b3e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e57 : x = (k x y) := by
          first
          | (have i₁ := b3e56
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e56
          | exact resolve b3e56 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e56
        have b3e68 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X1 X2) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e17 X1 X2
             have i₂ := b3e17 X1 X0
             grind)
          | (have i₁ := b3e17 X0 X1
             have i₂ := b3e17 X0 (M.op X0 X0)
             grind)
          | exact superpose b3e17 b3e17
          | (have j0 := b3e17 X1 X2
             have j1 := b3e17 X1 X2
             grind)
          | exact resolve b3e17 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b3e72 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e15 X0 X0
             have i₂ := b3e17 X0 X1
             grind)
          | (have i₁ := b3e15 X0 X1
             have i₂ := b3e17 X0 (M.op X0 X1)
             grind)
          | exact superpose b3e17 b3e15
          | (have j0 := b3e15 X1 X0
             have j1 := b3e17 X1 X0
             grind)
          | (have r₁ := b3e15 X1 X1
             have r₂ := b3e17 X1 X1
             grind)
          | (have r₁ := b3e15 (M.op X0 X0) X1
             have r₂ := b3e17 X0 (M.op (M.op X0 X0) X1)
             grind)
          | (have r₁ := b3e15 X0 X1
             have r₂ := b3e17 X0 X1
             grind)
          | exact resolve b3e15 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e73 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X1 X1 X2
             have i₂ := b3e17 X1 X0
             grind)
          | (have i₁ := b3e12 X0 X1 X2
             have i₂ := b3e17 X0 (M.op X0 X1)
             grind)
          | exact superpose b3e17 b3e12
          | (have j1 := b3e17 X1 X0
             grind)
          | exact resolve b3e12 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e75 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b3e77 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (M.op X1 (M.op X1 X2)) ∨ (M.op X3 X0) = (k X3 X0) ∨ (M.op X3 X0) = X3 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 X1 X2 X3
             have i₂ := b3e17 X3 X0
             grind)
          | (have i₁ := b3e12 X0 X1 X2
             have i₂ := b3e17 X0 (M.op X2 X2)
             grind)
          | exact superpose b3e17 b3e12
          | (have j1 := b3e17 X3 X0
             grind)
          | exact resolve b3e12 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e78 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e75 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e75
        have b3e81 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (M.op X1 (M.op X1 X2)) ∨ (M.op X3 X0) = (k X3 X0) := by
          intro X0 X1 X2 X3
          first
          | (have j0 := b3e77 X0 X1 X2 X3
             have j1 := b3e15 X3 X0
             grind)
          | (have r₁ := b3e77 X0 (M.op X2 X0) X2 X3
             have r₂ := b3e15 (M.op X2 X0) (M.op (M.op X2 X0) X2)
             grind)
          | (have r₁ := b3e77 X1 X1 X2 X0
             have r₂ := b3e15 X0 X1
             grind)
          | exact resolve b3e77 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e77
        have b3e83 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b3e78 X0 X1
             have j1 := b3e15 X1 X0
             grind)
          | (have r₁ := b3e78 X1 X0
             have r₂ := b3e15 X0 X1
             grind)
          | exact resolve b3e78 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e78
        have b3e85 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b3e73 X0 X1 X2
             have j1 := b3e15 X1 X0
             grind)
          | (have r₁ := b3e73 X1 X0 X2
             have r₂ := b3e15 X0 X1
             grind)
          | exact resolve b3e73 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e73
        have b3e86 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e72 X0 X1
             have j1 := b3e15 X1 X0
             grind)
          | (have r₁ := b3e72 (M.op X0 X1) (k X0 X1)
             have r₂ := b3e15 X0 X1
             grind)
          | (have r₁ := b3e72 (k X0 X1) (M.op X0 X1)
             have r₂ := b3e15 X0 X1
             grind)
          | (have r₁ := b3e72 (M.op (k X1 X1) X1) X1
             have r₂ := b3e15 (k X1 X1) X1
             grind)
          | exact resolve b3e72 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e72
        have b3e87 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1 X2
          first
          | (have j0 := b3e68 X0 X1 X2
             have j1 := b3e15 X1 X2
             grind)
          | (have r₁ := b3e68 (M.op X0 X1) X1 X0
             have r₂ := b3e15 X0 X1
             grind)
          | (have r₁ := b3e68 X0 X1 (M.op X0 X1)
             have r₂ := b3e15 X0 X1
             grind)
          | (have r₁ := b3e68 X0 X0 X1
             have r₂ := b3e15 X0 X1
             grind)
          | exact resolve b3e68 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e68
        have b3e89 : ∀ X0 X2 X3 : G, (M.op X2 X0) = (M.op X2 y) ∨ (M.op X3 X0) = (k X3 X0) := by
          intro X0 X2 X3
          first
          | (have i₁ := b3e81 X0 x X2 X3
             have i₂ := b3e33 x X2
             grind)
          | exact superpose b3e33 b3e81
          | (have j0 := b3e81 X0 x X2 X3
             grind)
          | exact resolve b3e81 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e81
        have b3e91 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b3e87 X0 X1 X2
             have j1 := b3e15 X1 X2
             grind)
          | (have r₁ := b3e87 (M.op X0 X1) X1 X0
             have r₂ := b3e15 X0 X1
             grind)
          | (have r₁ := b3e87 X0 X1 (M.op X0 X1)
             have r₂ := b3e15 X0 X1
             grind)
          | (have r₁ := b3e87 X1 X0 X2
             have r₂ := b3e15 X0 X1
             grind)
          | exact resolve b3e87 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e87
        have b3e94 : (M.op (σ x) (σ x)) = (M.op (σ y) y) := by
          first
          | (have i₁ := b3e33 (σ x) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e33
          | exact resolve b3e33 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e95 : ∀ X0 X1 : G, (M.op (M.op X1 X0) y) = (M.op X1 (M.op X0 y)) := by
          intro X0 X1
          first
          | (have i₁ := b3e33 X1 (M.op X1 X0)
             have i₂ := b3e33 X1 X0
             grind)
          | exact superpose b3e33 b3e33
          | exact resolve b3e33 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e101 : ∀ X0 X2 : G, (M.op X0 y) = (M.op X0 (M.op X2 X2)) := by
          intro X0 X2
          first
          | (have i₁ := b3e12 x X0 X2
             have i₂ := b3e33 x X0
             grind)
          | exact superpose b3e33 b3e12
          | exact resolve b3e12 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e147 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e13 (k (τ X0) X1)
             have i₂ := b3e25 X0 X1
             grind)
          | exact superpose b3e25 b3e13
          | exact resolve b3e13 b3e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e156 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e13 (k X0 (τ X1))
             have i₂ := b3e26 X1 X0
             grind)
          | exact superpose b3e26 b3e13
          | exact resolve b3e13 b3e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e446 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e147 X1 (τ X0)
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e147
          | exact resolve b3e147 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e463 : ∀ X0 : G, (M.op y y) = (M.op (M.op (σ y) y) (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e38 (σ x) X0
             have i₂ := b3e94
             grind)
          | exact superpose b3e94 b3e38
          | exact resolve b3e38 b3e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38 b3e94
        have b3e526 : (M.op y y) = (M.op (M.op (σ y) y) y) := by
          first
          | (have i₁ := b3e463 x
             have i₂ := b3e101 (M.op (σ y) y) x
             grind)
          | exact superpose b3e101 b3e463
          | exact resolve b3e463 b3e101
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e463
        have b3e548 : (M.op y y) = (M.op (σ y) (M.op y y)) := by
          first
          | (have i₁ := b3e526
             have i₂ := b3e95 y (σ y)
             grind)
          | exact superpose b3e95 b3e526
          | exact resolve b3e526 b3e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e526
        have b3e562 : (M.op (σ x) (σ x)) = (M.op y y) := by
          first
          | (have i₁ := b3e548
             have i₂ := b3e28 y
             grind)
          | exact superpose b3e28 b3e548
          | exact resolve b3e548 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28 b3e548
        have b3e583 : (σ x) ≠ (M.op y y) ∨ (M.op y y) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b3e15 (σ x) (σ x)
             have i₂ := b3e562
             grind)
          | exact superpose b3e562 b3e15
          | exact resolve b3e15 b3e562
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e596 : (M.op y y) = (σ (k x x)) ∨ (σ x) ≠ (M.op y y) := by
          first
          | (have i₁ := b3e583
             have i₂ := b3e18 x x
             grind)
          | exact superpose b3e18 b3e583
          | exact resolve b3e583 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e583
        have b3e687 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b3e83 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e83
        have b3e759 : ∀ X0 X1 : G, (k X0 (M.op X0 y)) = X0 ∨ (M.op X0 (M.op X0 y)) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          grind
        clear b3e89
        have b3e818 : ∀ X0 X1 : G, (k X0 (M.op X0 y)) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e759 X0 X1
             have j1 := b3e687 X0 (M.op X0 y)
             grind)
          | (have r₁ := b3e759 X0 X1
             have r₂ := b3e687 X0 (M.op X0 y)
             grind)
          | exact resolve b3e759 b3e687
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e759
        have b3e933 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 (M.op X0 (M.op X1 X1)))) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 (M.op X0 (M.op X1 X1)))) := by
          intro X0 X1
          grind
        clear b3e29
        have b3e1018 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 (M.op X0 (M.op X1 X1)))) := by
          intro X0 X1
          first
          | (have j0 := b3e933 X0 X1
             have j1 := b3e687 (M.op X0 X0) (M.op X0 (M.op X0 (M.op X1 X1)))
             grind)
          | (have r₁ := b3e933 X0 X1
             have r₂ := b3e687 (M.op X0 X0) (M.op X0 (M.op X0 (M.op X1 X1)))
             grind)
          | exact resolve b3e933 b3e687
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e687 b3e933
        have b3e1137 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op X1 X1) y)) := by
          intro X0 X1
          first
          | (have i₁ := b3e1018 X0 X1
             have i₂ := b3e33 X0 (M.op X1 X1)
             grind)
          | exact superpose b3e33 b3e1018
          | exact resolve b3e1018 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1018
        have b3e1243 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X1 (M.op X1 y))) := by
          intro X0 X1
          first
          | (have i₁ := b3e1137 X0 X1
             have i₂ := b3e95 X1 X1
             grind)
          | exact superpose b3e95 b3e1137
          | exact resolve b3e1137 b3e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e95 b3e1137
        have b3e1314 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op y y)) := by
          intro X0
          first
          | (have i₁ := b3e1243 X0 x
             have i₂ := b3e33 x y
             grind)
          | exact superpose b3e33 b3e1243
          | exact resolve b3e1243 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1243
        have b3e2347 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = X0 ∨ (k X1 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e85 X0 X0 X2
             have i₂ := b3e17 X0 X1
             grind)
          | (have i₁ := b3e85 X0 X1 X2
             have i₂ := b3e17 X0 (M.op X1 X0)
             grind)
          | exact superpose b3e17 b3e85
          | (have j0 := b3e85 X0 X1 X2
             have j1 := b3e17 X1 X0
             grind)
          | exact resolve b3e85 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e85
        have b3e2532 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = X0 ∨ (k X1 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b3e2347 X0 X1 X2
             have j1 := b3e15 X1 X0
             grind)
          | (have r₁ := b3e2347 X0 X0 X2
             have r₂ := b3e15 X0 (M.op X2 X2)
             grind)
          | (have r₁ := b3e2347 (M.op (M.op X1 (M.op X2 X2)) X1) X1 X2
             have r₂ := b3e15 (M.op X1 (M.op X2 X2)) X1
             grind)
          | (have r₁ := b3e2347 (M.op (k X1 X1) X1) X1 X2
             have r₂ := b3e15 (k X1 X1) X1
             grind)
          | exact resolve b3e2347 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2347
        have b3e2593 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X1) = X0 ∨ (M.op X1 y) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e2532 X0 X1 x
             have i₂ := b3e101 X1 x
             grind)
          | exact superpose b3e101 b3e2532
          | (have j0 := b3e2532 X0 X1 x
             grind)
          | exact resolve b3e2532 b3e101
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e101 b3e2532
        have b3e2868 : ∀ X0 : G, (σ (M.op x y)) = (σ x) ∨ y = X0 ∨ (k x X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b3e52
             have i₂ := b3e91 y x X0
             grind)
          | exact superpose b3e91 b3e52
          | (have j1 := b3e91 y x X0
             grind)
          | exact resolve b3e52 b3e91
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52 b3e91
        have b3e2875 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ y = X0 := by
          intro X0
          first
          | (have j0 := b3e2868 X0
             grind)
          | (have r₁ := b3e2868 X0
             have r₂ := b3e24
             grind)
          | exact resolve b3e2868 b3e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2868
        have b3e3476 : (M.op y y) = (σ (k x x)) ∨ (σ x) = (M.op y y) ∨ (σ x) = (M.op y y) := by
          first
          | (have i₁ := b3e69 x x
             have i₂ := b3e562
             grind)
          | exact superpose b3e562 b3e69
          | exact resolve b3e69 b3e562
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e562
        have b3e3479 : ∀ X0 X1 : G, (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 ∨ (σ X1) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e69 X0 X0
             have i₂ := b3e17 (σ X0) X1
             grind)
          | (have i₁ := b3e69 X0 X1
             have i₂ := b3e17 X0 (M.op (σ X0) (σ X1))
             grind)
          | exact superpose b3e17 b3e69
          | (have j1 := b3e17 (σ X1) X0
             grind)
          | exact resolve b3e69 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e3531 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e13 X1
             have i₂ := b3e69 X0 X1
             grind)
          | exact superpose b3e69 b3e13
          | (have j1 := b3e69 X0 X1
             grind)
          | exact resolve b3e13 b3e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e69
        have b3e3597 : ∀ X0 X1 : G, (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
          intro X0 X1
          first
          | (have j0 := b3e3479 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3479
        have b3e3600 : (M.op y y) = (σ (k x x)) ∨ (σ x) = (M.op y y) := by grind
        clear b3e3476
        have b3e3652 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b3e3597 X0 X1
             have j1 := b3e15 (σ X1) X0
             grind)
          | (have r₁ := b3e3597 (M.op (σ (k X1 X1)) X1) X1
             have r₂ := b3e15 (σ (k X1 X1)) X1
             grind)
          | (have r₁ := b3e3597 (M.op (σ X1) X1) X1
             have r₂ := b3e15 (σ X1) X1
             grind)
          | (have r₁ := b3e3597 X1 X1
             have r₂ := b3e15 (σ X1) X1
             grind)
          | exact resolve b3e3597 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3597
        have b3e3654 : (M.op y y) = (σ (k x x)) := by
          first
          | (have r₁ := b3e3600
             have r₂ := b3e596
             grind)
          | exact resolve b3e3600 b3e596
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e596 b3e3600
        have b3e3696 : (M.op y y) = (σ (M.op x x)) ∨ x = y := by
          first
          | (have i₁ := b3e3654
             have i₂ := b3e2875 x
             grind)
          | exact superpose b3e2875 b3e3654
          | (have j1 := b3e2875 x
             grind)
          | exact resolve b3e3654 b3e2875
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2875
        have b3e3702 : (k x x) = (τ (M.op y y)) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e3654
             grind)
          | exact superpose b3e3654 b3e13
          | exact resolve b3e13 b3e3654
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e3719 : (σ y) = (M.op y y) ∨ x = y := by
          first
          | (have i₁ := b3e3696
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e3696
          | exact resolve b3e3696 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3696
        have b3e4114 : (k x x) = (τ (σ y)) ∨ x = y := by
          first
          | (have i₁ := b3e3702
             have i₂ := b3e3719
             grind)
          | exact superpose b3e3719 b3e3702
          | exact resolve b3e3702 b3e3719
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3719
        have b3e4161 : y = (k x x) ∨ x = y := by
          first
          | (have i₁ := b3e4114
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e4114
          | exact resolve b3e4114 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4114
        have b3e4166 : y = (k x x) := by
          first
          | (have r₁ := b3e4161
             have r₂ := b3e45
             grind)
          | exact resolve b3e4161 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45 b3e4161
        have b3e4454 : (σ y) = (M.op y y) := by
          first
          | (have i₁ := b3e3654
             have i₂ := b3e4166
             grind)
          | exact superpose b3e4166 b3e3654
          | exact resolve b3e3654 b3e4166
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e4575 : (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b3e1314 y
             have i₂ := b3e4454
             grind)
          | exact superpose b3e4454 b3e1314
          | exact resolve b3e1314 b3e4454
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1314
        have b3e4592 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b3e4575
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e4575
          | exact resolve b3e4575 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4575
        have b3e4769 : (τ (σ y)) = (k y y) := by
          first
          | (have i₁ := b3e13 (k y y)
             have i₂ := b3e4592
             grind)
          | exact superpose b3e4592 b3e13
          | exact resolve b3e13 b3e4592
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e4770 : ∀ X0 : G, (σ (k (k y y) X0)) = (k (σ y) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 (k y y) X0
             have i₂ := b3e4592
             grind)
          | exact superpose b3e4592 b3e18
          | exact resolve b3e18 b3e4592
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4592
        have b3e4784 : ∀ X0 : G, (σ (k (k y y) X0)) = (σ (k y X0)) := by
          intro X0
          first
          | (have i₁ := b3e4770 X0
             have i₂ := b3e18 y X0
             grind)
          | exact superpose b3e18 b3e4770
          | exact resolve b3e4770 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4770
        have b3e4785 : y = (k y y) := by
          first
          | (have i₁ := b3e4769
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e4769
          | exact resolve b3e4769 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4769
        have b3e4825 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) y))) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e156 X0 (M.op (σ X0) y)
             have i₂ := b3e818 (σ X0) X1
             grind)
          | exact superpose b3e818 b3e156
          | (have j1 := b3e818 (σ X0) X1
             grind)
          | exact resolve b3e156 b3e818
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e818
        have b3e4839 : ∀ X0 X1 : G, (k X0 (τ (M.op (σ X0) y))) = X0 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e4825 X0 X1
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e4825
          | (have j0 := b3e4825 X0 X1
             grind)
          | exact resolve b3e4825 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4825
        have b3e4866 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e17 y y
             have i₂ := b3e4785
             grind)
          | exact superpose b3e4785 b3e17
          | (have j0 := b3e17 y y
             grind)
          | exact resolve b3e17 b3e4785
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e4869 : y = (M.op y y) := by grind
        clear b3e4866
        have b3e4948 : y = (σ y) := by
          first
          | (have i₁ := b3e4454
             have i₂ := b3e4869
             grind)
          | exact superpose b3e4869 b3e4454
          | exact resolve b3e4454 b3e4869
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e4950 : (k x x) = (τ y) := by
          first
          | (have i₁ := b3e3702
             have i₂ := b3e4869
             grind)
          | exact superpose b3e4869 b3e3702
          | exact resolve b3e3702 b3e4869
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3702
        have b3e4992 : y = (τ y) := by
          first
          | (have i₁ := b3e4950
             have i₂ := b3e4166
             grind)
          | exact superpose b3e4166 b3e4950
          | exact resolve b3e4950 b3e4166
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4166 b3e4950
        have b3e5077 : (σ x) = (M.op (σ x) y) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e4948
             grind)
          | exact superpose b3e4948 b3e22
          | exact resolve b3e22 b3e4948
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e5083 : ∀ X0 : G, (k y (σ X0)) = (σ (k y X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 y X0
             have i₂ := b3e4948
             grind)
          | exact superpose b3e4948 b3e18
          | exact resolve b3e18 b3e4948
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e5093 : ∀ X0 : G, (k y (τ X0)) = (τ (k y X0)) := by
          intro X0
          first
          | (have i₁ := b3e156 y X0
             have i₂ := b3e4948
             grind)
          | exact superpose b3e4948 b3e156
          | exact resolve b3e156 b3e4948
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e12962 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e3652 X0 (τ X0)
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e3652
          | (have j0 := b3e3652 X1 (τ X0)
             grind)
          | exact resolve b3e3652 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3652
        have b3e13101 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e12962 X0 X1
             have i₂ := b3e26 X0 (τ X0)
             grind)
          | exact superpose b3e26 b3e12962
          | (have j0 := b3e12962 X0 X1
             grind)
          | exact resolve b3e12962 b3e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e12962
        have b3e13121 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e13101 X0 X1
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e13101
          | (have j0 := b3e13101 X0 X1
             grind)
          | exact resolve b3e13101 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e13101
        have b3e13136 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b3e13121 X0 X1
             have j1 := b3e86 X1 X0
             grind)
          | (have r₁ := b3e13121 X0 X1
             have r₂ := b3e86 (k X0 X0) X1
             grind)
          | (have r₁ := b3e13121 X0 X0
             have r₂ := b3e86 X0 (k X0 X0)
             grind)
          | (have r₁ := b3e13121 X0 X1
             have r₂ := b3e86 (M.op X0 X1) (k X0 X1)
             grind)
          | exact resolve b3e13121 b3e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e86 b3e13121
        have b3e22160 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op (k y y) X0)) ∨ (k (k y y) (k y y)) = X0 ∨ (M.op (k y y) y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e4784 X0
             have i₂ := b3e2593 X0 (k y y)
             grind)
          | exact superpose b3e2593 b3e4784
          | (have j1 := b3e2593 X0 (k y y)
             grind)
          | exact resolve b3e4784 b3e2593
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2593 b3e4784
        have b3e22268 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op y X0)) ∨ (k (k y y) (k y y)) = X0 ∨ (M.op (k y y) y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e22160 X0
             have i₂ := b3e4785
             grind)
          | exact superpose b3e4785 b3e22160
          | (have j0 := b3e22160 X0
             grind)
          | exact resolve b3e22160 b3e4785
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e22160
        have b3e22305 : ∀ X0 : G, (k y y) = X0 ∨ (σ (k y X0)) = (σ (M.op y X0)) ∨ (M.op (k y y) y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e22268 X0
             have i₂ := b3e4785
             grind)
          | exact superpose b3e4785 b3e22268
          | (have j0 := b3e22268 X0
             grind)
          | exact resolve b3e22268 b3e4785
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e22268
        have b3e22325 : ∀ X0 : G, y = X0 ∨ (σ (k y X0)) = (σ (M.op y X0)) ∨ (M.op (k y y) y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e22305 X0
             have i₂ := b3e4785
             grind)
          | exact superpose b3e4785 b3e22305
          | (have j0 := b3e22305 X0
             grind)
          | exact resolve b3e22305 b3e4785
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e22305
        have b3e22337 : ∀ X0 : G, (M.op y y) = X0 ∨ y = X0 ∨ (σ (k y X0)) = (σ (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b3e22325 X0
             have i₂ := b3e4785
             grind)
          | exact superpose b3e4785 b3e22325
          | (have j0 := b3e22325 X0
             grind)
          | exact resolve b3e22325 b3e4785
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e22325
        have b3e22344 : ∀ X0 : G, (σ y) = X0 ∨ y = X0 ∨ (σ (k y X0)) = (σ (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b3e22337 X0
             have i₂ := b3e4454
             grind)
          | exact superpose b3e4454 b3e22337
          | (have j0 := b3e22337 X0
             grind)
          | exact resolve b3e22337 b3e4454
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e22337
        have b3e22348 : ∀ X0 : G, y = X0 ∨ y = X0 ∨ (σ (k y X0)) = (σ (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b3e22344 X0
             have i₂ := b3e4948
             grind)
          | exact superpose b3e4948 b3e22344
          | (have j0 := b3e22344 X0
             grind)
          | exact resolve b3e22344 b3e4948
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e22344
        have b3e22349 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op y X0)) ∨ y = X0 := by
          intro X0
          first
          | (have j0 := b3e22348 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e22348
        have b3e32907 : ∀ X0 : G, (σ X0) = (M.op y y) ∨ (k x X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b3e3654
             have i₂ := b3e13136 x X0
             grind)
          | (have i₁ := b3e3654
             have i₂ := b3e13136 X0 (k x x)
             grind)
          | exact superpose b3e13136 b3e3654
          | (have j1 := b3e13136 x X0
             grind)
          | exact resolve b3e3654 b3e13136
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3654
        have b3e32916 : ∀ X0 : G, (τ X0) = (k y (τ y)) ∨ (M.op y X0) = (k y X0) := by
          intro X0
          first
          | (have i₁ := b3e5093 y
             have i₂ := b3e13136 y X0
             grind)
          | (have i₁ := b3e5093 X0
             have i₂ := b3e13136 X0 (k y X0)
             grind)
          | exact superpose b3e13136 b3e5093
          | (have j1 := b3e13136 y X0
             grind)
          | exact resolve b3e5093 b3e13136
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5093 b3e13136
        have b3e33048 : ∀ X0 : G, (τ X0) = (k y y) ∨ (M.op y X0) = (k y X0) := by
          intro X0
          first
          | (have i₁ := b3e32916 X0
             have i₂ := b3e4992
             grind)
          | exact superpose b3e4992 b3e32916
          | (have j0 := b3e32916 X0
             grind)
          | exact resolve b3e32916 b3e4992
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32916
        have b3e33052 : ∀ X0 : G, (σ X0) = (σ y) ∨ (k x X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b3e32907 X0
             have i₂ := b3e4454
             grind)
          | exact superpose b3e4454 b3e32907
          | (have j0 := b3e32907 X0
             grind)
          | exact resolve b3e32907 b3e4454
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32907
        have b3e33121 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ (τ X0) = y := by
          intro X0
          first
          | (have i₁ := b3e33048 X0
             have i₂ := b3e4785
             grind)
          | exact superpose b3e4785 b3e33048
          | (have j0 := b3e33048 X0
             grind)
          | exact resolve b3e33048 b3e4785
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4785 b3e33048
        have b3e33122 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ (σ X0) = y := by
          intro X0
          first
          | (have i₁ := b3e33052 X0
             have i₂ := b3e4948
             grind)
          | exact superpose b3e4948 b3e33052
          | (have j0 := b3e33052 X0
             grind)
          | exact resolve b3e33052 b3e4948
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33052
        have b3e33256 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = X1 ∨ (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e3531 (τ X0) X1
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e3531
          | exact resolve b3e3531 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3531
        have b3e33397 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (τ (M.op X0 X0)) = X1 ∨ (M.op X0 (σ X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e33256 X0 X1
             have i₂ := b3e25 X0 X1
             grind)
          | exact superpose b3e25 b3e33256
          | (have j0 := b3e33256 X0 X1
             grind)
          | exact resolve b3e33256 b3e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25 b3e33256
        have b3e33441 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (τ (M.op X0 X0)) = X1 := by
          intro X0 X1
          first
          | (have j0 := b3e33397 X0 X1
             have j1 := b3e15 X0 (σ X1)
             grind)
          | (have r₁ := b3e33397 X0 (M.op (τ (M.op X0 X0)) X1)
             have r₂ := b3e15 (τ (M.op X0 X0)) X1
             grind)
          | (have r₁ := b3e33397 X0 X1
             have r₂ := b3e15 X0 (σ X1)
             grind)
          | exact resolve b3e33397 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33397
        have b3e34725 : ∀ X0 : G, (k (σ x) X0) = (σ (M.op x (τ X0))) ∨ (σ (τ X0)) = y := by
          intro X0
          first
          | (have i₁ := b3e26 X0 x
             have i₂ := b3e33122 (τ X0)
             grind)
          | exact superpose b3e33122 b3e26
          | (have j1 := b3e33122 (τ X0)
             grind)
          | exact resolve b3e26 b3e33122
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26 b3e33122
        have b3e34737 : ∀ X0 : G, (k (σ x) X0) = (σ (M.op x (τ X0))) ∨ y = X0 := by
          intro X0
          first
          | (have i₁ := b3e34725 X0
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e34725
          | (have j0 := b3e34725 X0
             grind)
          | exact resolve b3e34725 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34725
        have b3e36289 : ∀ X0 : G, (M.op y (σ X0)) = (σ (k y X0)) ∨ (τ (σ X0)) = y := by
          intro X0
          first
          | (have i₁ := b3e5083 X0
             have i₂ := b3e33121 (σ X0)
             grind)
          | exact superpose b3e33121 b3e5083
          | (have j1 := b3e33121 (σ X0)
             grind)
          | exact resolve b3e5083 b3e33121
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e36349 : ∀ X0 : G, (M.op y (σ X0)) = (σ (k y X0)) ∨ y = X0 := by
          intro X0
          first
          | (have i₁ := b3e36289 X0
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e36289
          | (have j0 := b3e36289 X0
             grind)
          | exact resolve b3e36289 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e36289
        have b3e73089 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op y X0)) ∨ y = X0 ∨ y = X0 := by
          intro X0
          first
          | (have i₁ := b3e22349 X0
             have i₂ := b3e36349 X0
             grind)
          | exact superpose b3e36349 b3e22349
          | (have j0 := b3e22349 X0
             have j1 := b3e36349 X0
             grind)
          | exact resolve b3e22349 b3e36349
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e22349 b3e36349
        have b3e73212 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op y X0)) ∨ y = X0 := by
          intro X0
          first
          | (have j0 := b3e73089 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e73089
        have b3e75139 : ∀ X0 : G, (M.op y X0) = (τ (M.op y (σ X0))) ∨ y = X0 := by
          intro X0
          first
          | (have i₁ := b3e13 (M.op y X0)
             have i₂ := b3e73212 X0
             grind)
          | exact superpose b3e73212 b3e13
          | (have j1 := b3e73212 X0
             grind)
          | exact resolve b3e13 b3e73212
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e73212
        have b3e84874 : ∀ X0 : G, (τ y) = X0 ∨ (M.op x (σ X0)) = (k x (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e33441 x X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e33441
          | (have j0 := b3e33441 x X0
             grind)
          | exact resolve b3e33441 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33441
        have b3e85011 : ∀ X0 : G, (M.op x (σ X0)) = (k x (σ X0)) ∨ y = X0 := by
          intro X0
          first
          | (have i₁ := b3e84874 X0
             have i₂ := b3e4992
             grind)
          | exact superpose b3e4992 b3e84874
          | (have j0 := b3e84874 X0
             grind)
          | exact resolve b3e84874 b3e4992
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e84874
        have b3e85288 : ∀ X0 : G, (k (τ x) X0) = (τ (M.op x (σ X0))) ∨ y = X0 := by
          intro X0
          first
          | (have i₁ := b3e147 x X0
             have i₂ := b3e85011 X0
             grind)
          | exact superpose b3e85011 b3e147
          | (have j1 := b3e85011 X0
             grind)
          | exact resolve b3e147 b3e85011
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e147 b3e85011
        have b3e97916 : ∀ X0 : G, (τ (M.op x X0)) = (k (τ x) (τ X0)) ∨ (τ X0) = y := by
          intro X0
          first
          | (have i₁ := b3e85288 (τ X0)
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e85288
          | (have j0 := b3e85288 (τ X0)
             grind)
          | exact resolve b3e85288 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e85288
        have b3e98004 : ∀ X0 : G, (τ (M.op x X0)) = (τ (k x X0)) ∨ (τ X0) = y := by
          intro X0
          first
          | (have i₁ := b3e97916 X0
             have i₂ := b3e446 X0 x
             grind)
          | exact superpose b3e446 b3e97916
          | (have j0 := b3e97916 X0
             grind)
          | exact resolve b3e97916 b3e446
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e446 b3e97916
        have b3e102926 : ∀ X0 : G, (τ (k (σ x) X0)) = (M.op x (τ X0)) ∨ y = X0 := by
          intro X0
          first
          | (have i₁ := b3e13 (M.op x (τ X0))
             have i₂ := b3e34737 X0
             grind)
          | exact superpose b3e34737 b3e13
          | (have j1 := b3e34737 X0
             grind)
          | exact resolve b3e13 b3e34737
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34737
        have b3e103075 : ∀ X0 : G, (k x (τ X0)) = (M.op x (τ X0)) ∨ y = X0 := by
          intro X0
          first
          | (have i₁ := b3e102926 X0
             have i₂ := b3e156 x X0
             grind)
          | exact superpose b3e156 b3e102926
          | (have j0 := b3e102926 X0
             grind)
          | exact resolve b3e102926 b3e156
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e156 b3e102926
        have b3e144262 : ∀ X0 : G, (τ x) = (τ (M.op x (τ (M.op (σ x) y)))) ∨ y = (τ (τ (M.op (σ x) y))) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e98004 (τ (M.op (σ x) y))
             have i₂ := b3e4839 x X0
             grind)
          | exact superpose b3e4839 b3e98004
          | (have j0 := b3e98004 (τ (M.op (σ x) y))
             have j1 := b3e4839 x X0
             grind)
          | exact resolve b3e98004 b3e4839
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4839 b3e98004
        have b3e144331 : ∀ X0 : G, (τ x) = (τ (M.op x (τ (σ x)))) ∨ y = (τ (τ (M.op (σ x) y))) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e144262 X0
             have i₂ := b3e5077
             grind)
          | exact superpose b3e5077 b3e144262
          | (have j0 := b3e144262 X0
             grind)
          | exact resolve b3e144262 b3e5077
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e144262
        have b3e144463 : ∀ X0 : G, (τ x) = (τ (M.op x x)) ∨ y = (τ (τ (M.op (σ x) y))) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e144331 X0
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e144331
          | (have j0 := b3e144331 X0
             grind)
          | exact resolve b3e144331 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e144331
        have b3e144544 : ∀ X0 : G, (τ x) = (τ y) ∨ y = (τ (τ (M.op (σ x) y))) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e144463 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e144463
          | (have j0 := b3e144463 X0
             grind)
          | exact resolve b3e144463 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e144463
        have b3e144597 : ∀ X0 : G, y = (τ x) ∨ y = (τ (τ (M.op (σ x) y))) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e144544 X0
             have i₂ := b3e4992
             grind)
          | exact superpose b3e4992 b3e144544
          | (have j0 := b3e144544 X0
             grind)
          | exact resolve b3e144544 b3e4992
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4992 b3e144544
        have b3e144627 : ∀ X0 : G, y = (τ (τ (σ x))) ∨ y = (τ x) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e144597 X0
             have i₂ := b3e5077
             grind)
          | exact superpose b3e5077 b3e144597
          | (have j0 := b3e144597 X0
             grind)
          | exact resolve b3e144597 b3e5077
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e144597
        have b3e144643 : ∀ X0 : G, y = (τ x) ∨ y = (τ x) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e144627 X0
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e144627
          | (have j0 := b3e144627 X0
             grind)
          | exact resolve b3e144627 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e144627
        have b3e144644 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) ∨ y = (τ x) := by
          intro X0
          first
          | (have j0 := b3e144643 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e144643
        have b3e147766 : (σ (k y x)) = (M.op y (σ x)) ∨ y = (τ x) := by
          first
          | (have i₁ := b3e5083 x
             have i₂ := b3e144644 y
             grind)
          | exact superpose b3e144644 b3e5083
          | exact resolve b3e5083 b3e144644
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5083 b3e144644
        have b3e148913 : (M.op y (σ x)) = (σ (M.op y x)) ∨ y = (τ x) ∨ y = (τ x) := by
          first
          | (have i₁ := b3e147766
             have i₂ := b3e33121 x
             grind)
          | exact superpose b3e33121 b3e147766
          | (have j1 := b3e33121 x
             grind)
          | exact resolve b3e147766 b3e33121
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33121 b3e147766
        have b3e149092 : (M.op y (σ x)) = (σ (M.op y x)) ∨ y = (τ x) := by grind
        clear b3e148913
        have b3e152934 : (M.op y (M.op y x)) = (τ (M.op y (M.op y (σ x)))) ∨ y = (M.op y x) ∨ y = (τ x) := by
          first
          | (have i₁ := b3e75139 (M.op y x)
             have i₂ := b3e149092
             grind)
          | exact superpose b3e149092 b3e75139
          | (have j0 := b3e75139 (M.op y x)
             grind)
          | exact resolve b3e75139 b3e149092
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e75139
        have b3e152940 : (τ (M.op (σ x) y)) = (M.op y (M.op y x)) ∨ y = (M.op y x) ∨ y = (τ x) := by
          first
          | (have i₁ := b3e152934
             have i₂ := b3e33 y (σ x)
             grind)
          | exact superpose b3e33 b3e152934
          | exact resolve b3e152934 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e152934
        have b3e152988 : (M.op x y) = (τ (M.op (σ x) y)) ∨ y = (M.op y x) ∨ y = (τ x) := by
          first
          | (have i₁ := b3e152940
             have i₂ := b3e33 y x
             grind)
          | exact superpose b3e33 b3e152940
          | exact resolve b3e152940 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e152940
        have b3e153027 : (M.op x y) = (τ (σ x)) ∨ y = (M.op y x) ∨ y = (τ x) := by
          first
          | (have i₁ := b3e152988
             have i₂ := b3e5077
             grind)
          | exact superpose b3e5077 b3e152988
          | exact resolve b3e152988 b3e5077
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e152988
        have b3e153043 : x = (M.op x y) ∨ y = (M.op y x) ∨ y = (τ x) := by
          first
          | (have i₁ := b3e153027
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e153027
          | exact resolve b3e153027 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e153027
        have b3e153049 : y = (M.op y x) ∨ y = (τ x) := by
          first
          | (have r₁ := b3e153043
             have r₂ := b3e20
             grind)
          | exact resolve b3e153043 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e153043
        have b3e154371 : (σ y) = (M.op y (σ x)) ∨ y = (τ x) ∨ y = (τ x) := by
          first
          | (have i₁ := b3e149092
             have i₂ := b3e153049
             grind)
          | exact superpose b3e153049 b3e149092
          | exact resolve b3e149092 b3e153049
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e149092
        have b3e154382 : (M.op x y) = (M.op y y) ∨ y = (τ x) := by
          first
          | (have i₁ := b3e33 y x
             have i₂ := b3e153049
             grind)
          | exact superpose b3e153049 b3e33
          | exact resolve b3e33 b3e153049
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e153049
        have b3e154412 : (σ y) = (M.op y (σ x)) ∨ y = (τ x) := by grind
        clear b3e154371
        have b3e154423 : (M.op x y) = (σ y) ∨ y = (τ x) := by
          first
          | (have i₁ := b3e154382
             have i₂ := b3e4454
             grind)
          | exact superpose b3e4454 b3e154382
          | exact resolve b3e154382 b3e4454
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e154382
        have b3e154432 : y = (M.op y (σ x)) ∨ y = (τ x) := by
          first
          | (have i₁ := b3e154412
             have i₂ := b3e4948
             grind)
          | exact superpose b3e4948 b3e154412
          | exact resolve b3e154412 b3e4948
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e154412
        have b3e154442 : y = (M.op x y) ∨ y = (τ x) := by
          first
          | (have i₁ := b3e154423
             have i₂ := b3e4948
             grind)
          | exact superpose b3e4948 b3e154423
          | exact resolve b3e154423 b3e4948
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e154423
        have b3e156592 : (σ x) ≠ (σ y) ∨ y = (τ x) := by
          first
          | (have i₁ := b3e24
             have i₂ := b3e154442
             grind)
          | exact superpose b3e154442 b3e24
          | exact resolve b3e24 b3e154442
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24 b3e154442
        have b3e156722 : y ≠ (σ x) ∨ y = (τ x) := by
          first
          | (have i₁ := b3e156592
             have i₂ := b3e4948
             grind)
          | exact superpose b3e4948 b3e156592
          | exact resolve b3e156592 b3e4948
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e156592
        have b3e160330 : (M.op y y) = (M.op (σ x) y) ∨ y = (τ x) := by
          first
          | (have i₁ := b3e33 y (σ x)
             have i₂ := b3e154432
             grind)
          | exact superpose b3e154432 b3e33
          | exact resolve b3e33 b3e154432
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33 b3e154432
        have b3e160382 : (σ x) = (M.op y y) ∨ y = (τ x) := by
          first
          | (have i₁ := b3e160330
             have i₂ := b3e5077
             grind)
          | exact superpose b3e5077 b3e160330
          | exact resolve b3e160330 b3e5077
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5077 b3e160330
        have b3e160410 : (σ x) = (σ y) ∨ y = (τ x) := by
          first
          | (have i₁ := b3e160382
             have i₂ := b3e4454
             grind)
          | exact superpose b3e4454 b3e160382
          | exact resolve b3e160382 b3e4454
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4454 b3e160382
        have b3e160430 : y = (σ x) ∨ y = (τ x) := by
          first
          | (have i₁ := b3e160410
             have i₂ := b3e4948
             grind)
          | exact superpose b3e4948 b3e160410
          | exact resolve b3e160410 b3e4948
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4948 b3e160410
        have b3e160440 : y = (τ x) := by
          first
          | (have r₁ := b3e160430
             have r₂ := b3e156722
             grind)
          | exact resolve b3e160430 b3e156722
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e156722 b3e160430
        have b3e161667 : (M.op x y) = (k x y) ∨ x = y := by
          first
          | (have i₁ := b3e103075 x
             have i₂ := b3e160440
             grind)
          | exact superpose b3e160440 b3e103075
          | (have j0 := b3e103075 x
             grind)
          | exact resolve b3e103075 b3e160440
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e103075 b3e160440
        have b3e161668 : x = (M.op x y) ∨ x = y := by
          first
          | (have i₁ := b3e161667
             have i₂ := b3e57
             grind)
          | exact superpose b3e57 b3e161667
          | exact resolve b3e161667 b3e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e57 b3e161667
        have b3e161683 : x = y := by
          first
          | (have r₁ := b3e161668
             have r₂ := b3e20
             grind)
          | exact resolve b3e161668 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e161668
        have b3e163315 : x ≠ (M.op x x) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e161683
             grind)
          | exact superpose b3e161683 b3e20
          | exact resolve b3e20 b3e161683
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e163424 : x = (M.op x x) := by
          first
          | (have i₁ := b3e4869
             have i₂ := b3e161683
             grind)
          | exact superpose b3e161683 b3e4869
          | exact resolve b3e4869 b3e161683
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4869 b3e161683
        have b3e163622 : False := by grind
        exact b3e163622
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (M.op X2 X2)) := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ (M.op x y) := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e26 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b4e31 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k (τ X0) X1)
               have i₂ := b4e26 X0 X1
               grind)
            | exact superpose b4e26 b4e14
            | exact resolve b4e14 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e32 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e13 x x X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e33 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ x) (σ x) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op X1 (M.op X0 (M.op X0 X1))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X1 (M.op X2 X2) X3
               have i₂ := b4e13 X0 X1 X2
               grind)
            | (have i₁ := b4e13 X0 (M.op X0 X1) X2
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e38 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 X1 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 X1 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e43 : ∀ X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op X1 (M.op X1 (σ y))) := by
            intro X1 X2 X3
            first
            | (have i₁ := b4e35 x X1 X2 X3
               have i₂ := b4e39 x X1
               grind)
            | exact superpose b4e39 b4e35
            | exact resolve b4e35 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e44 : ∀ X2 X3 : G, (M.op (M.op X2 X2) (M.op X3 X3)) = (M.op (σ y) (σ y)) := by
            intro X2 X3
            first
            | (have i₁ := b4e43 x X2 X3
               have i₂ := b4e39 x (σ y)
               grind)
            | exact superpose b4e39 b4e43
            | exact resolve b4e43 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43
          have b4e45 : (M.op x y) = (M.op x (σ y)) := by
            first
            | (have i₁ := b4e32 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e32
            | exact resolve b4e32 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e54 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
            first
            | (have i₁ := b4e16 (σ x) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e58 : (σ x) ≠ (σ y) ∨ (σ y) = (σ (k x x)) := by
            first
            | (have i₁ := b4e54
               have i₂ := b4e19 x x
               grind)
            | exact superpose b4e19 b4e54
            | exact resolve b4e54 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54
          have b4e77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b4e80 : ∀ X0 : G, (σ y) = X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b4e24
               have i₂ := b4e18 (σ x) X0
               grind)
            | (have i₁ := b4e24
               have i₂ := b4e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b4e18 b4e24
            | (have j1 := b4e18 (σ x) X0
               grind)
            | exact resolve b4e24 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e81 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X0 X0
               have i₂ := b4e18 X0 X1
               grind)
            | (have i₁ := b4e16 X0 X1
               have i₂ := b4e18 X0 (M.op X0 X1)
               grind)
            | exact superpose b4e18 b4e16
            | (have j0 := b4e16 X1 X0
               have j1 := b4e18 X1 X0
               grind)
            | (have r₁ := b4e16 X1 X1
               have r₂ := b4e18 X1 X1
               grind)
            | (have r₁ := b4e16 (M.op X0 X0) X1
               have r₂ := b4e18 X0 (M.op (M.op X0 X0) X1)
               grind)
            | (have r₁ := b4e16 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | exact resolve b4e16 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e84 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b4e86 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (M.op X1 (M.op X1 X2)) ∨ (M.op X3 X0) = (k X3 X0) ∨ (M.op X3 X0) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X1 X2 X3
               have i₂ := b4e18 X3 X0
               grind)
            | (have i₁ := b4e13 X0 X1 X2
               have i₂ := b4e18 X0 (M.op X2 X2)
               grind)
            | exact superpose b4e18 b4e13
            | (have j1 := b4e18 X3 X0
               grind)
            | exact resolve b4e13 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e87 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e84 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e84
          have b4e90 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (M.op X1 (M.op X1 X2)) ∨ (M.op X3 X0) = (k X3 X0) := by
            intro X0 X1 X2 X3
            first
            | (have j0 := b4e86 X0 X1 X2 X3
               have j1 := b4e16 X3 X0
               grind)
            | (have r₁ := b4e86 X0 (M.op X2 X0) X2 X3
               have r₂ := b4e16 (M.op X2 X0) (M.op (M.op X2 X0) X2)
               grind)
            | (have r₁ := b4e86 X1 X1 X2 X0
               have r₂ := b4e16 X0 X1
               grind)
            | exact resolve b4e86 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e86
          have b4e92 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e87 X0 X1
               have j1 := b4e16 X1 X0
               grind)
            | (have r₁ := b4e87 X1 X0
               have r₂ := b4e16 X0 X1
               grind)
            | exact resolve b4e87 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e87
          have b4e95 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e81 X0 X1
               have j1 := b4e16 X1 X0
               grind)
            | (have r₁ := b4e81 (M.op X0 X1) (k X0 X1)
               have r₂ := b4e16 X0 X1
               grind)
            | (have r₁ := b4e81 (k X0 X1) (M.op X0 X1)
               have r₂ := b4e16 X0 X1
               grind)
            | (have r₁ := b4e81 (M.op (k X1 X1) X1) X1
               have r₂ := b4e16 (k X1 X1) X1
               grind)
            | exact resolve b4e81 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e81
          have b4e96 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ y) = X0 := by
            intro X0
            first
            | (have j0 := b4e80 X0
               have j1 := b4e16 (σ x) X0
               grind)
            | (have r₁ := b4e80 (M.op (σ y) x)
               have r₂ := b4e16 (σ y) x
               grind)
            | (have r₁ := b4e80 x
               have r₂ := b4e16 (σ x) x
               grind)
            | exact resolve b4e80 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e80
          have b4e100 : ∀ X0 X2 X3 : G, (M.op X2 X0) = (M.op X2 (σ y)) ∨ (M.op X3 X0) = (k X3 X0) := by
            intro X0 X2 X3
            first
            | (have i₁ := b4e90 X0 x X2 X3
               have i₂ := b4e39 x X2
               grind)
            | exact superpose b4e39 b4e90
            | (have j0 := b4e90 X0 x X2 X3
               grind)
            | exact resolve b4e90 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e90
          have b4e108 : ∀ X0 X1 : G, (M.op (M.op X1 X0) y) = (M.op X1 (M.op X0 y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e38 X1 (M.op X1 X0)
               have i₂ := b4e38 X1 X0
               grind)
            | exact superpose b4e38 b4e38
            | exact resolve b4e38 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e110 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = (M.op (M.op X2 X2) y) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e38 X1 (M.op X2 X2)
               have i₂ := b4e13 X0 X1 X2
               grind)
            | (have i₁ := b4e38 X0 (M.op X0 X1)
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e38
            | exact resolve b4e38 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e111 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e38 X1 X1
               have i₂ := b4e18 X1 X0
               grind)
            | (have i₁ := b4e38 X0 X1
               have i₂ := b4e18 X0 (M.op X0 X1)
               grind)
            | exact superpose b4e18 b4e38
            | (have j1 := b4e18 X1 X0
               grind)
            | exact resolve b4e38 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e114 : ∀ X0 X2 : G, (M.op X0 y) = (M.op X0 (M.op X2 X2)) := by
            intro X0 X2
            first
            | (have i₁ := b4e13 x X0 X2
               have i₂ := b4e38 x X0
               grind)
            | exact superpose b4e38 b4e13
            | exact resolve b4e13 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e117 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 y)) = (M.op (M.op X1 X0) (M.op X2 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 (M.op X1 X0) X2
               have i₂ := b4e38 X1 X0
               grind)
            | exact superpose b4e38 b4e13
            | exact resolve b4e13 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e118 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 y) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e111 X0 X1
               have j1 := b4e16 X1 X0
               grind)
            | (have r₁ := b4e111 X1 X0
               have r₂ := b4e16 X0 X1
               grind)
            | exact resolve b4e111 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e111
          have b4e119 : ∀ X1 X2 : G, (M.op X1 (M.op X1 (σ y))) = (M.op (M.op X2 X2) y) := by
            intro X1 X2
            first
            | (have i₁ := b4e110 x X1 X2
               have i₂ := b4e39 x X1
               grind)
            | exact superpose b4e39 b4e110
            | exact resolve b4e110 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e110
          have b4e123 : ∀ X1 X2 : G, (M.op X1 (M.op X1 (σ y))) = (M.op X2 (M.op X2 y)) := by
            intro X1 X2
            first
            | (have i₁ := b4e119 X1 X2
               have i₂ := b4e108 X2 X2
               grind)
            | exact superpose b4e108 b4e119
            | exact resolve b4e119 b4e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e119
          have b4e125 : ∀ X1 : G, (M.op X1 (M.op X1 (σ y))) = (M.op y (σ y)) := by
            intro X1
            first
            | (have i₁ := b4e123 X1 x
               have i₂ := b4e39 x y
               grind)
            | exact superpose b4e39 b4e123
            | exact resolve b4e123 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e123
          have b4e126 : (M.op (σ y) (σ y)) = (M.op y (σ y)) := by
            first
            | (have i₁ := b4e125 x
               have i₂ := b4e39 x (σ y)
               grind)
            | exact superpose b4e39 b4e125
            | exact resolve b4e125 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e125
          have b4e127 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e114 X0 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e114
            | exact resolve b4e114 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e130 : ∀ X0 X1 X2 : G, (M.op X1 y) = (M.op X1 X0) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X2 X0) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e114 X1 X2
               have i₂ := b4e18 X2 X0
               grind)
            | (have i₁ := b4e114 X0 X2
               have i₂ := b4e18 X0 (M.op X2 X2)
               grind)
            | exact superpose b4e18 b4e114
            | (have j1 := b4e18 X2 X0
               grind)
            | exact resolve b4e114 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e150 : ∀ X0 X1 X2 : G, (M.op X1 y) = (M.op X1 X0) ∨ (M.op X2 X0) = (k X2 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e130 X0 X1 X2
               have j1 := b4e16 X2 X0
               grind)
            | (have r₁ := b4e130 X1 X1 X0
               have r₂ := b4e16 X0 X1
               grind)
            | exact resolve b4e130 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e130
          have b4e184 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e127 (σ x)
               grind)
            | exact superpose b4e127 b4e20
            | exact resolve b4e20 b4e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e797 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e31 X1 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e31
            | exact resolve b4e31 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31
          have b4e813 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e92 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e92
          have b4e837 : ∀ X0 X1 X2 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op X2 X2)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e44 X1 X2
               have i₂ := b4e18 X1 X0
               grind)
            | (have i₁ := b4e44 X2 x
               have i₂ := b4e18 X0 (M.op X2 X2)
               grind)
            | exact superpose b4e18 b4e44
            | (have j1 := b4e18 X1 X0
               grind)
            | exact resolve b4e44 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e872 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (σ y) (σ y))) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op (σ y) (σ y))) := by
            intro X0
            grind
          have b4e882 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (M.op X0 X0) (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 (M.op x x) (M.op x x)
               have i₂ := b4e44 x x
               grind)
            | exact superpose b4e44 b4e16
            | (have r₁ := b4e16 (M.op (σ y) (σ y)) (M.op x x)
               have r₂ := b4e44 (σ y) x
               grind)
            | exact resolve b4e16 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e885 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op y (σ y)) ∨ (M.op (σ y) (σ y)) = (k (M.op X0 X0) (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e882 X0 X1
               have i₂ := b4e126
               grind)
            | exact superpose b4e126 b4e882
            | (have j0 := b4e882 X0 X1
               grind)
            | exact resolve b4e882 b4e126
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e882
          have b4e890 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (σ y) (σ y))) := by
            intro X0
            first
            | (have j0 := b4e872 X0
               have j1 := b4e813 (M.op X0 X0) (M.op (σ y) (σ y))
               grind)
            | (have r₁ := b4e872 X0
               have r₂ := b4e813 (M.op X0 X0) (M.op (σ y) (σ y))
               grind)
            | exact resolve b4e872 b4e813
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e813 b4e872
          have b4e916 : ∀ X0 X1 X2 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op X2 X2)) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e837 X0 X1 X2
               have j1 := b4e16 X1 X0
               grind)
            | (have r₁ := b4e837 (M.op (σ y) (σ y)) X1 X2
               have r₂ := b4e16 (M.op (σ y) (σ y)) (M.op X2 X2)
               grind)
            | (have r₁ := b4e837 X1 X0 X2
               have r₂ := b4e16 X0 X1
               grind)
            | exact resolve b4e837 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e837
          have b4e922 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op y y) ∨ (M.op (σ y) (σ y)) = (k (M.op X0 X0) (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e885 X0 X1
               have i₂ := b4e127 y
               grind)
            | exact superpose b4e127 b4e885
            | (have j0 := b4e885 X0 X1
               grind)
            | (have r₁ := b4e885 y X1
               have r₂ := b4e127 y
               grind)
            | exact resolve b4e885 b4e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e885
          have b4e927 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op y (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e890 X0
               have i₂ := b4e126
               grind)
            | exact superpose b4e126 b4e890
            | exact resolve b4e890 b4e126
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e890
          have b4e952 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (M.op X0 y) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e916 X0 X1 x
               have i₂ := b4e114 X0 x
               grind)
            | exact superpose b4e114 b4e916
            | (have j0 := b4e916 X0 X1 x
               grind)
            | exact resolve b4e916 b4e114
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e916
          have b4e958 : ∀ X0 X1 : G, (M.op y (σ y)) = (k (M.op X0 X0) (M.op X1 X1)) ∨ (M.op X0 X0) ≠ (M.op y y) := by
            intro X0 X1
            first
            | (have i₁ := b4e922 X0 X1
               have i₂ := b4e126
               grind)
            | exact superpose b4e126 b4e922
            | (have j0 := b4e922 X0 X1
               grind)
            | exact resolve b4e922 b4e126
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e922
          have b4e963 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b4e927 X0
               have i₂ := b4e127 y
               grind)
            | exact superpose b4e127 b4e927
            | exact resolve b4e927 b4e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e927
          have b4e981 : ∀ X0 X1 : G, (M.op X0 y) = (M.op y (σ y)) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e952 X0 X1
               have i₂ := b4e126
               grind)
            | exact superpose b4e126 b4e952
            | (have j0 := b4e952 X0 X1
               grind)
            | exact resolve b4e952 b4e126
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e952
          have b4e986 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op y y) ∨ (M.op y y) = (k (M.op X0 X0) (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e958 X0 X1
               have i₂ := b4e127 y
               grind)
            | exact superpose b4e127 b4e958
            | (have j0 := b4e958 X0 X1
               grind)
            | exact resolve b4e958 b4e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e958
          have b4e1001 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 y) = (M.op y y) := by
            intro X0 X1
            first
            | (have i₁ := b4e981 X0 X1
               have i₂ := b4e127 y
               grind)
            | exact superpose b4e127 b4e981
            | (have j0 := b4e981 X0 X1
               grind)
            | exact resolve b4e981 b4e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e981
          have b4e1043 : (σ y) ≠ (M.op y (σ y)) ∨ (M.op y (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b4e16 (σ y) (σ y)
               have i₂ := b4e126
               grind)
            | exact superpose b4e126 b4e16
            | exact resolve b4e16 b4e126
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1046 : (σ y) ≠ (M.op y y) ∨ (M.op y (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b4e1043
               have i₂ := b4e127 y
               grind)
            | exact superpose b4e127 b4e1043
            | exact resolve b4e1043 b4e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1043
          have b4e1062 : (M.op y (σ y)) = (σ (k y y)) ∨ (σ y) ≠ (M.op y y) := by
            first
            | (have i₁ := b4e1046
               have i₂ := b4e19 y y
               grind)
            | exact superpose b4e19 b4e1046
            | exact resolve b4e1046 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1046
          have b4e1069 : (σ y) ≠ (M.op y y) ∨ (M.op y y) = (σ (k y y)) := by
            first
            | (have i₁ := b4e1062
               have i₂ := b4e127 y
               grind)
            | exact superpose b4e127 b4e1062
            | exact resolve b4e1062 b4e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1062
          have b4e3033 : ∀ X0 X1 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e23
               have i₂ := b4e100 X0 (σ x) X1
               grind)
            | (have i₁ := b4e23
               have i₂ := b4e100 (σ y) (σ x) x
               grind)
            | exact superpose b4e100 b4e23
            | (have j1 := b4e100 X0 x X1
               grind)
            | exact resolve b4e23 b4e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e100
          have b4e5042 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e77 x x
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e77
            | exact resolve b4e77 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e5044 : (M.op y (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op y (σ y)) ∨ (σ y) = (M.op y (σ y)) := by
            first
            | (have i₁ := b4e77 y y
               have i₂ := b4e126
               grind)
            | exact superpose b4e126 b4e77
            | exact resolve b4e77 b4e126
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e126
          have b4e5048 : ∀ X0 X1 : G, (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 ∨ (σ X1) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e77 X0 X0
               have i₂ := b4e18 (σ X0) X1
               grind)
            | (have i₁ := b4e77 X0 X1
               have i₂ := b4e18 X0 (M.op (σ X0) (σ X1))
               grind)
            | exact superpose b4e18 b4e77
            | (have j1 := b4e18 (σ X1) X0
               grind)
            | exact resolve b4e77 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e77
          have b4e5177 : ∀ X0 X1 : G, (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
            intro X0 X1
            first
            | (have j0 := b4e5048 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5048
          have b4e5179 : (M.op y (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op y (σ y)) := by grind
          clear b4e5044
          have b4e5180 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
          clear b4e5042
          have b4e5247 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e5177 X0 X1
               have j1 := b4e16 (σ X1) X0
               grind)
            | (have r₁ := b4e5177 (M.op (σ (k X1 X1)) X1) X1
               have r₂ := b4e16 (σ (k X1 X1)) X1
               grind)
            | (have r₁ := b4e5177 (M.op (σ X1) X1) X1
               have r₂ := b4e16 (σ X1) X1
               grind)
            | (have r₁ := b4e5177 X1 X1
               have r₂ := b4e16 (σ X1) X1
               grind)
            | exact resolve b4e5177 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5177
          have b4e5248 : (M.op y y) = (σ (k y y)) ∨ (σ y) = (M.op y (σ y)) := by
            first
            | (have i₁ := b4e5179
               have i₂ := b4e127 y
               grind)
            | exact superpose b4e127 b4e5179
            | exact resolve b4e5179 b4e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5179
          have b4e5249 : (σ y) = (σ (k x x)) := by
            first
            | (have r₁ := b4e5180
               have r₂ := b4e58
               grind)
            | exact resolve b4e5180 b4e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e58 b4e5180
          have b4e5291 : (σ y) = (M.op y y) ∨ (M.op y y) = (σ (k y y)) := by
            first
            | (have i₁ := b4e5248
               have i₂ := b4e127 y
               grind)
            | exact superpose b4e127 b4e5248
            | exact resolve b4e5248 b4e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5248
          have b4e5306 : (M.op y y) = (σ (k y y)) := by
            first
            | (have r₁ := b4e5291
               have r₂ := b4e1069
               grind)
            | exact resolve b4e5291 b4e1069
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1069 b4e5291
          have b4e5329 : (k x x) = (τ (σ y)) := by
            first
            | (have i₁ := b4e14 (k x x)
               have i₂ := b4e5249
               grind)
            | exact superpose b4e5249 b4e14
            | exact resolve b4e14 b4e5249
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e5330 : ∀ X0 : G, (σ (k (k x x) X0)) = (k (σ y) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 (k x x) X0
               have i₂ := b4e5249
               grind)
            | exact superpose b4e5249 b4e19
            | exact resolve b4e19 b4e5249
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e5344 : ∀ X0 : G, (σ (k y X0)) = (σ (k (k x x) X0)) := by
            intro X0
            first
            | (have i₁ := b4e5330 X0
               have i₂ := b4e19 y X0
               grind)
            | exact superpose b4e19 b4e5330
            | exact resolve b4e5330 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5330
          have b4e5345 : y = (k x x) := by
            first
            | (have i₁ := b4e5329
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e5329
            | exact resolve b4e5329 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5329
          have b4e5558 : (k y y) = (τ (M.op y y)) := by
            first
            | (have i₁ := b4e14 (k y y)
               have i₂ := b4e5306
               grind)
            | exact superpose b4e5306 b4e14
            | exact resolve b4e14 b4e5306
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e5559 : ∀ X0 : G, (σ (k (k y y) X0)) = (k (M.op y y) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 (k y y) X0
               have i₂ := b4e5306
               grind)
            | exact superpose b4e5306 b4e19
            | exact resolve b4e19 b4e5306
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e7072 : ∀ X0 : G, (σ x) ≠ (σ y) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e3033 (σ x) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e3033
            | (have j0 := b4e3033 (σ x) X0
               grind)
            | exact resolve b4e3033 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3033
          have b4e8398 : (k (M.op y y) (M.op y y)) = (σ (k (k y y) (k y y))) := by
            first
            | (have i₁ := b4e5559 (k y y)
               have i₂ := b4e5306
               grind)
            | exact superpose b4e5306 b4e5559
            | exact resolve b4e5559 b4e5306
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5559
          have b4e8436 : (M.op y y) = (σ (k (k y y) (k y y))) := by
            first
            | (have i₁ := b4e8398
               have i₂ := b4e963 y
               grind)
            | exact superpose b4e963 b4e8398
            | exact resolve b4e8398 b4e963
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8398
          have b4e8862 : (τ (M.op y y)) = (k (k y y) (k y y)) := by
            first
            | (have i₁ := b4e14 (k (k y y) (k y y))
               have i₂ := b4e8436
               grind)
            | exact superpose b4e8436 b4e14
            | exact resolve b4e14 b4e8436
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8436
          have b4e8893 : (k y y) = (k (k y y) (k y y)) := by
            first
            | (have i₁ := b4e8862
               have i₂ := b4e5558
               grind)
            | exact superpose b4e5558 b4e8862
            | exact resolve b4e8862 b4e5558
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5558 b4e8862
          have b4e8982 : (k y y) = (M.op (k y y) (k y y)) ∨ (k y y) = (M.op (k y y) (k y y)) ∨ (k y y) = (M.op (k y y) (k y y)) := by
            first
            | (have i₁ := b4e18 (k y y) (k y y)
               have i₂ := b4e8893
               grind)
            | exact superpose b4e8893 b4e18
            | (have j0 := b4e18 (k y y) (k y y)
               grind)
            | exact resolve b4e18 b4e8893
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8893
          have b4e8992 : (k y y) = (M.op (k y y) (k y y)) := by grind
          clear b4e8982
          have b4e9300 : (M.op (k y y) y) = (M.op (k y y) (k y y)) := by
            first
            | (have i₁ := b4e38 (k y y) (k y y)
               have i₂ := b4e8992
               grind)
            | exact superpose b4e8992 b4e38
            | exact resolve b4e38 b4e8992
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e9308 : ∀ X0 : G, (M.op (k y y) (M.op X0 X0)) = (M.op (k y y) (M.op (k y y) y)) := by
            intro X0
            first
            | (have i₁ := b4e117 (k y y) (k y y) X0
               have i₂ := b4e8992
               grind)
            | exact superpose b4e8992 b4e117
            | exact resolve b4e117 b4e8992
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e117
          have b4e9315 : ∀ X0 : G, (M.op y (σ y)) = (M.op (k y y) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e9308 X0
               have i₂ := b4e39 (k y y) y
               grind)
            | exact superpose b4e39 b4e9308
            | exact resolve b4e9308 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9308
          have b4e9322 : (k y y) = (M.op (k y y) y) := by
            first
            | (have i₁ := b4e9300
               have i₂ := b4e8992
               grind)
            | exact superpose b4e8992 b4e9300
            | exact resolve b4e9300 b4e8992
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9300
          have b4e9345 : (M.op y (σ y)) = (M.op (k y y) y) := by
            first
            | (have i₁ := b4e9315 x
               have i₂ := b4e114 (k y y) x
               grind)
            | exact superpose b4e114 b4e9315
            | exact resolve b4e9315 b4e114
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9315
          have b4e9362 : (M.op y (σ y)) = (k y y) := by
            first
            | (have i₁ := b4e9345
               have i₂ := b4e9322
               grind)
            | exact superpose b4e9322 b4e9345
            | exact resolve b4e9345 b4e9322
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9345
          have b4e9369 : (M.op y y) = (k y y) := by
            first
            | (have i₁ := b4e9362
               have i₂ := b4e127 y
               grind)
            | exact superpose b4e127 b4e9362
            | exact resolve b4e9362 b4e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9362
          have b4e9546 : (M.op y y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e5306
               have i₂ := b4e9369
               grind)
            | exact superpose b4e9369 b4e5306
            | exact resolve b4e5306 b4e9369
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5306 b4e9369
          have b4e9654 : (M.op y y) = (τ (M.op y y)) := by
            first
            | (have i₁ := b4e14 (M.op y y)
               have i₂ := b4e9546
               grind)
            | exact superpose b4e9546 b4e14
            | exact resolve b4e14 b4e9546
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e17704 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e5247 X0 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e5247
            | (have j0 := b4e5247 X1 (τ X0)
               grind)
            | exact resolve b4e5247 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5247
          have b4e17879 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e17704 X0 X1
               have i₂ := b4e27 X0 (τ X0)
               grind)
            | exact superpose b4e27 b4e17704
            | (have j0 := b4e17704 X0 X1
               grind)
            | exact resolve b4e17704 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e17704
          have b4e17913 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e17879 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e17879
            | (have j0 := b4e17879 X0 X1
               grind)
            | exact resolve b4e17879 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e17879
          have b4e17932 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e17913 X0 X1
               have j1 := b4e95 X1 X0
               grind)
            | (have r₁ := b4e17913 X0 X1
               have r₂ := b4e95 (k X0 X0) X1
               grind)
            | (have r₁ := b4e17913 X0 X0
               have r₂ := b4e95 X0 (k X0 X0)
               grind)
            | (have r₁ := b4e17913 X0 X1
               have r₂ := b4e95 (M.op X0 X1) (k X0 X1)
               grind)
            | exact resolve b4e17913 b4e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e95 b4e17913
          have b4e19144 : ∀ X0 X1 : G, (σ X0) = (k X1 (σ (τ X1))) ∨ (k (τ X1) X0) = (M.op (τ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e26 X1 (τ X1)
               have i₂ := b4e17932 (τ X1) X0
               grind)
            | (have i₁ := b4e26 X0 X1
               have i₂ := b4e17932 X0 (k (τ X0) X1)
               grind)
            | exact superpose b4e17932 b4e26
            | (have j1 := b4e17932 (τ X1) X0
               grind)
            | exact resolve b4e26 b4e17932
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26
          have b4e19153 : ∀ X0 : G, (M.op x X0) = (k x X0) ∨ (σ X0) = (σ y) := by
            intro X0
            first
            | (have i₁ := b4e5249
               have i₂ := b4e17932 x X0
               grind)
            | (have i₁ := b4e5249
               have i₂ := b4e17932 X0 (k x x)
               grind)
            | exact superpose b4e17932 b4e5249
            | (have j1 := b4e17932 x X0
               grind)
            | exact resolve b4e5249 b4e17932
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5249
          have b4e19159 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op y X0) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b4e8992
               have i₂ := b4e17932 y x
               grind)
            | (have i₁ := b4e8992
               have i₂ := b4e17932 X0 (k y y)
               grind)
            | exact superpose b4e17932 b4e8992
            | (have j1 := b4e17932 y X0
               grind)
            | exact resolve b4e8992 b4e17932
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8992
          have b4e19162 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b4e9322
               have i₂ := b4e17932 y x
               grind)
            | (have i₁ := b4e9322
               have i₂ := b4e17932 X0 (k y y)
               grind)
            | exact superpose b4e17932 b4e9322
            | (have j1 := b4e17932 y X0
               grind)
            | exact resolve b4e9322 b4e17932
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9322
          have b4e19186 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op y y)) ∨ (M.op y y) = (k (M.op X0 X0) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e963 X0
               have i₂ := b4e17932 (M.op X0 X0) (M.op y y)
               grind)
            | exact superpose b4e17932 b4e963
            | (have j1 := b4e17932 (M.op X0 X0) (M.op y y)
               grind)
            | exact resolve b4e963 b4e17932
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e963
          have b4e19265 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) y) ∨ (M.op y y) = (k (M.op X0 X0) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e19186 X0
               have i₂ := b4e114 (M.op X0 X0) y
               grind)
            | exact superpose b4e114 b4e19186
            | (have j0 := b4e19186 X0
               grind)
            | exact resolve b4e19186 b4e114
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e19186
          have b4e19276 : ∀ X0 X1 : G, (σ X0) = (k X1 X1) ∨ (k (τ X1) X0) = (M.op (τ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e19144 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e19144
            | (have j0 := b4e19144 X0 X1
               grind)
            | exact resolve b4e19144 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e19144
          have b4e19332 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 y)) ∨ (M.op y y) = (k (M.op X0 X0) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e19265 X0
               have i₂ := b4e108 X0 X0
               grind)
            | exact superpose b4e108 b4e19265
            | (have j0 := b4e19265 X0
               grind)
            | exact resolve b4e19265 b4e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e19265
          have b4e19366 : ∀ X0 : G, (M.op X0 X0) = (M.op y (σ y)) ∨ (M.op y y) = (k (M.op X0 X0) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e19332 X0
               have i₂ := b4e39 X0 y
               grind)
            | exact superpose b4e39 b4e19332
            | (have j0 := b4e19332 X0
               grind)
            | exact resolve b4e19332 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e19332
          have b4e19383 : ∀ X0 : G, (M.op X0 X0) = (M.op y y) ∨ (M.op y y) = (k (M.op X0 X0) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e19366 X0
               have i₂ := b4e127 y
               grind)
            | exact superpose b4e127 b4e19366
            | (have j0 := b4e19366 X0
               grind)
            | exact resolve b4e19366 b4e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e19366
          have b4e19392 : ∀ X0 : G, (M.op y y) = (k (M.op X0 X0) (M.op X0 X0)) := by
            intro X0
            first
            | (have j0 := b4e19383 X0
               have j1 := b4e986 X0 X0
               grind)
            | (have r₁ := b4e19383 X0
               have r₂ := b4e986 X0 x
               grind)
            | (have r₁ := b4e19383 y
               have r₂ := b4e986 y x
               grind)
            | exact resolve b4e19383 b4e986
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e986 b4e19383
          have b4e19535 : ∀ X0 X1 : G, (k X0 X0) = (M.op y y) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e19392 X0
               have i₂ := b4e18 X0 X1
               grind)
            | (have i₁ := b4e19392 X0
               have i₂ := b4e18 X0 (M.op X0 X0)
               grind)
            | exact superpose b4e18 b4e19392
            | (have j1 := b4e18 X1 X0
               grind)
            | exact resolve b4e19392 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e19392
          have b4e19706 : ∀ X0 X1 : G, (k X0 X0) = (M.op y y) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e19535 X0 X1
               have j1 := b4e16 X1 X0
               grind)
            | (have r₁ := b4e19535 X1 X0
               have r₂ := b4e16 X0 X1
               grind)
            | exact resolve b4e19535 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e19535
          have b4e20506 : ∀ X0 : G, (k (σ x) X0) = (σ (M.op x (τ X0))) ∨ (σ (τ X0)) = (σ y) := by
            intro X0
            first
            | (have i₁ := b4e27 X0 x
               have i₂ := b4e19153 (τ X0)
               grind)
            | exact superpose b4e19153 b4e27
            | (have j1 := b4e19153 (τ X0)
               grind)
            | exact resolve b4e27 b4e19153
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27 b4e19153
          have b4e20514 : ∀ X0 : G, (k (σ x) X0) = (σ (M.op x (τ X0))) ∨ (σ y) = X0 := by
            intro X0
            first
            | (have i₁ := b4e20506 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e20506
            | (have j0 := b4e20506 X0
               grind)
            | exact resolve b4e20506 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e20506
          have b4e21614 : (σ x) = (σ y) ∨ (M.op y (σ x)) = (k y (σ x)) := by
            first
            | (have i₁ := b4e24
               have i₂ := b4e19159 (σ x)
               grind)
            | exact superpose b4e19159 b4e24
            | (have j1 := b4e19159 (σ x)
               grind)
            | exact resolve b4e24 b4e19159
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e19159
          have b4e21661 : (M.op y (σ x)) = (k y (σ x)) := by
            first
            | (have j1 := b4e7072 y
               grind)
            | (have r₁ := b4e21614
               have r₂ := b4e7072 x
               grind)
            | exact resolve b4e21614 b4e7072
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7072 b4e21614
          have b4e71478 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op y y) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e19706 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e19706
          have b4e90204 : ∀ X0 X1 : G, (M.op X0 y) ≠ (M.op y y) ∨ (k X0 X0) = (M.op X0 y) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e71478 y
               have i₂ := b4e150 X0 y x
               grind)
            | (have i₁ := b4e71478 X0
               have i₂ := b4e150 X0 X0 x
               grind)
            | exact superpose b4e150 b4e71478
            | (have j1 := b4e150 X0 X1 X1
               grind)
            | (have r₁ := b4e71478 y
               have r₂ := b4e150 y y x
               grind)
            | exact resolve b4e71478 b4e150
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e150 b4e71478
          have b4e90360 : ∀ X0 X1 : G, (k X0 X0) = (M.op X0 y) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e90204 X0 X1
               have j1 := b4e1001 X0 X1
               grind)
            | (have r₁ := b4e90204 X0 X1
               have r₂ := b4e1001 X0 X1
               grind)
            | (have r₁ := b4e90204 y X1
               have r₂ := b4e1001 y X1
               grind)
            | exact resolve b4e90204 b4e1001
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1001 b4e90204
          have b4e96801 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e90360 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e90360
          have b4e96813 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e96801 X0
               have j1 := b4e118 X0 X0
               grind)
            | (have r₁ := b4e96801 y
               have r₂ := b4e118 y y
               grind)
            | (have r₁ := b4e96801 X0
               have r₂ := b4e118 X0 X0
               grind)
            | exact resolve b4e96801 b4e118
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e118 b4e96801
          have b4e97612 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e17932 X0 X1
               have i₂ := b4e96813 X0
               grind)
            | exact superpose b4e96813 b4e17932
            | (have j0 := b4e17932 X0 X1
               grind)
            | exact resolve b4e17932 b4e96813
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e17932
          have b4e97649 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e96813 (σ X0)
               grind)
            | exact superpose b4e96813 b4e19
            | exact resolve b4e19 b4e96813
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e97655 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e797 X0 X0
               have i₂ := b4e96813 (τ X0)
               grind)
            | exact superpose b4e96813 b4e797
            | exact resolve b4e797 b4e96813
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e797
          have b4e97692 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e97655 X0
               have i₂ := b4e96813 X0
               grind)
            | exact superpose b4e96813 b4e97655
            | exact resolve b4e97655 b4e96813
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e97655
          have b4e97698 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e97649 X0
               have i₂ := b4e96813 X0
               grind)
            | exact superpose b4e96813 b4e97649
            | exact resolve b4e97649 b4e96813
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e97649
          have b4e98466 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (τ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e114 X1 (τ X0)
               have i₂ := b4e97692 X0
               grind)
            | exact superpose b4e97692 b4e114
            | exact resolve b4e114 b4e97692
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e98518 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) y) = (M.op (τ X0) (M.op (τ X0) y)) := by
            intro X0
            first
            | (have i₁ := b4e108 (τ X0) (τ X0)
               have i₂ := b4e97692 X0
               grind)
            | exact superpose b4e97692 b4e108
            | exact resolve b4e108 b4e97692
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e97692
          have b4e98562 : ∀ X0 : G, (M.op y (σ y)) = (M.op (τ (M.op X0 X0)) y) := by
            intro X0
            first
            | (have i₁ := b4e98518 X0
               have i₂ := b4e39 (τ X0) y
               grind)
            | exact superpose b4e39 b4e98518
            | exact resolve b4e98518 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e98518
          have b4e98634 : ∀ X0 : G, (M.op y y) = (M.op (τ (M.op X0 X0)) y) := by
            intro X0
            first
            | (have i₁ := b4e98562 X0
               have i₂ := b4e127 y
               grind)
            | exact superpose b4e127 b4e98562
            | exact resolve b4e98562 b4e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e98562
          have b4e100251 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (τ y)) := by
            intro X0
            first
            | (have i₁ := b4e98466 x X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e98466
            | exact resolve b4e98466 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e98466
          have b4e101553 : (σ (M.op x y)) = (k (σ x) y) ∨ y = (σ y) := by
            first
            | (have i₁ := b4e20514 y
               have i₂ := b4e100251 x
               grind)
            | exact superpose b4e100251 b4e20514
            | (have j0 := b4e20514 y
               grind)
            | exact resolve b4e20514 b4e100251
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e20514 b4e100251
          have b4e153623 : (σ (M.op x y)) = (M.op (σ x) y) ∨ y = (σ y) ∨ y = (σ y) := by
            first
            | (have i₁ := b4e96 y
               have i₂ := b4e101553
               grind)
            | exact superpose b4e101553 b4e96
            | (have j0 := b4e96 y
               grind)
            | exact resolve b4e96 b4e101553
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e96 b4e101553
          have b4e153641 : (σ (M.op x y)) = (M.op (σ x) y) ∨ y = (σ y) := by grind
          clear b4e153623
          have b4e153655 : y = (σ y) := by
            first
            | (have r₁ := b4e153641
               have r₂ := b4e184
               grind)
            | exact resolve b4e153641 b4e184
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e153641
          have b4e154298 : ∀ X0 : G, (σ (k y X0)) = (k y (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 y X0
               have i₂ := b4e153655
               grind)
            | exact superpose b4e153655 b4e19
            | exact resolve b4e19 b4e153655
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e153655
          have b4e155788 : (σ (k y x)) = (M.op y (σ x)) := by
            first
            | (have i₁ := b4e21661
               have i₂ := b4e154298 x
               grind)
            | exact superpose b4e154298 b4e21661
            | exact resolve b4e21661 b4e154298
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e21661
          have b4e155825 : ∀ X0 : G, (σ (k y X0)) = (M.op y (σ X0)) ∨ (σ X0) = (M.op y y) := by
            intro X0
            first
            | (have i₁ := b4e97612 y (σ X0)
               have i₂ := b4e154298 X0
               grind)
            | exact superpose b4e154298 b4e97612
            | (have j0 := b4e97612 y (σ X0)
               grind)
            | exact resolve b4e97612 b4e154298
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e97612 b4e154298
          have b4e157404 : (σ (M.op y x)) = (M.op y (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e155788
               have i₂ := b4e19162 x
               grind)
            | exact superpose b4e19162 b4e155788
            | (have j1 := b4e19162 x
               grind)
            | exact resolve b4e155788 b4e19162
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e19162 b4e155788
          have b4e157518 : (σ (M.op y x)) = (M.op y (σ x)) := by
            first
            | (have r₁ := b4e157404
               have r₂ := b4e21
               grind)
            | exact resolve b4e157404 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e157404
          have b4e157966 : (M.op y x) = (τ (M.op y (σ x))) := by
            first
            | (have i₁ := b4e14 (M.op y x)
               have i₂ := b4e157518
               grind)
            | exact superpose b4e157518 b4e14
            | exact resolve b4e14 b4e157518
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e157518
          have b4e225194 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (M.op (τ (σ X1)) X0) = (k (τ (σ X1)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 X1
               have i₂ := b4e19276 X0 (σ X1)
               grind)
            | exact superpose b4e19276 b4e19
            | (have j1 := b4e19276 X0 (σ X1)
               grind)
            | exact resolve b4e19 b4e19276
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e19276
          have b4e225251 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (M.op (τ (σ X1)) X0) = (k (τ (σ X1)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e225194 X0 X1
               have i₂ := b4e96813 X1
               grind)
            | exact superpose b4e96813 b4e225194
            | (have j0 := b4e225194 X0 X1
               grind)
            | exact resolve b4e225194 b4e96813
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e96813 b4e225194
          have b4e225329 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (σ X0) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e225251 X0 X0
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e225251
            | (have j0 := b4e225251 X0 X1
               grind)
            | exact resolve b4e225251 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e225251
          have b4e225629 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op (k x x) X0)) ∨ (σ X0) = (σ (M.op (k x x) (k x x))) := by
            intro X0
            first
            | (have i₁ := b4e5344 X0
               have i₂ := b4e225329 X0 (k x x)
               grind)
            | exact superpose b4e225329 b4e5344
            | (have j1 := b4e225329 X0 (k x x)
               grind)
            | exact resolve b4e5344 b4e225329
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5344 b4e225329
          have b4e225794 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op y X0)) ∨ (σ X0) = (σ (M.op (k x x) (k x x))) := by
            intro X0
            first
            | (have i₁ := b4e225629 X0
               have i₂ := b4e5345
               grind)
            | exact superpose b4e5345 b4e225629
            | (have j0 := b4e225629 X0
               grind)
            | exact resolve b4e225629 b4e5345
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e225629
          have b4e225891 : ∀ X0 : G, (σ X0) = (σ (M.op y y)) ∨ (σ (k y X0)) = (σ (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b4e225794 X0
               have i₂ := b4e5345
               grind)
            | exact superpose b4e5345 b4e225794
            | (have j0 := b4e225794 X0
               grind)
            | exact resolve b4e225794 b4e5345
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5345 b4e225794
          have b4e225945 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op y X0)) ∨ (σ X0) = (M.op y y) := by
            intro X0
            first
            | (have i₁ := b4e225891 X0
               have i₂ := b4e9546
               grind)
            | exact superpose b4e9546 b4e225891
            | (have j0 := b4e225891 X0
               grind)
            | exact resolve b4e225891 b4e9546
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9546 b4e225891
          have b4e265267 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op y X0)) ∨ (σ X0) = (M.op y y) ∨ (σ X0) = (M.op y y) := by
            intro X0
            first
            | (have i₁ := b4e225945 X0
               have i₂ := b4e155825 X0
               grind)
            | exact superpose b4e155825 b4e225945
            | (have j0 := b4e225945 X0
               have j1 := b4e155825 X0
               grind)
            | exact resolve b4e225945 b4e155825
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e155825 b4e225945
          have b4e265299 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op y X0)) ∨ (σ X0) = (M.op y y) := by
            intro X0
            first
            | (have j0 := b4e265267 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e265267
          have b4e271122 : ∀ X0 : G, (M.op y X0) = (τ (M.op y (σ X0))) ∨ (σ X0) = (M.op y y) := by
            intro X0
            first
            | (have i₁ := b4e14 (M.op y X0)
               have i₂ := b4e265299 X0
               grind)
            | exact superpose b4e265299 b4e14
            | (have j1 := b4e265299 X0
               grind)
            | exact resolve b4e14 b4e265299
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e265299
          have b4e271584 : ∀ X0 : G, (M.op y (τ X0)) = (τ (M.op y X0)) ∨ (M.op y y) = X0 := by
            intro X0
            first
            | (have i₁ := b4e271122 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e271122
            | exact resolve b4e271122 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e271122
          have b4e271832 : ∀ X0 : G, (M.op y X0) = (σ (M.op y (τ X0))) ∨ (M.op y y) = X0 := by
            intro X0
            first
            | (have i₁ := b4e15 (M.op y X0)
               have i₂ := b4e271584 X0
               grind)
            | exact superpose b4e271584 b4e15
            | (have j1 := b4e271584 X0
               grind)
            | exact resolve b4e15 b4e271584
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e271584
          have b4e272004 : (M.op y (M.op y (σ x))) = (σ (M.op y (M.op y x))) ∨ (M.op y y) = (M.op y (σ x)) := by
            first
            | (have i₁ := b4e271832 (M.op y (σ x))
               have i₂ := b4e157966
               grind)
            | exact superpose b4e157966 b4e271832
            | (have j0 := b4e271832 (M.op y (σ x))
               grind)
            | exact resolve b4e271832 b4e157966
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e271832
          have b4e272086 : (σ (M.op x (σ y))) = (M.op y (M.op y (σ x))) ∨ (M.op y y) = (M.op y (σ x)) := by
            first
            | (have i₁ := b4e272004
               have i₂ := b4e39 y x
               grind)
            | exact superpose b4e39 b4e272004
            | exact resolve b4e272004 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e272004
          have b4e272090 : (M.op (σ x) (σ y)) = (σ (M.op x (σ y))) ∨ (M.op y y) = (M.op y (σ x)) := by
            first
            | (have i₁ := b4e272086
               have i₂ := b4e39 y (σ x)
               grind)
            | exact superpose b4e39 b4e272086
            | exact resolve b4e272086 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e272086
          have b4e272092 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op y (σ x)) := by
            first
            | (have i₁ := b4e272090
               have i₂ := b4e45
               grind)
            | exact superpose b4e45 b4e272090
            | exact resolve b4e272090 b4e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e272090
          have b4e272094 : (M.op y y) = (M.op y (σ x)) := by
            first
            | (have r₁ := b4e272092
               have r₂ := b4e20
               grind)
            | exact resolve b4e272092 b4e20
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e272092
          have b4e272123 : (τ (M.op y y)) = (M.op y x) := by
            first
            | (have i₁ := b4e157966
               have i₂ := b4e272094
               grind)
            | exact superpose b4e272094 b4e157966
            | exact resolve b4e157966 b4e272094
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e157966
          have b4e272184 : (M.op (σ x) y) = (M.op y (M.op y y)) := by
            first
            | (have i₁ := b4e38 y (σ x)
               have i₂ := b4e272094
               grind)
            | exact superpose b4e272094 b4e38
            | exact resolve b4e38 b4e272094
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e272094
          have b4e272234 : (M.op (σ x) y) = (M.op y (σ y)) := by
            first
            | (have i₁ := b4e272184
               have i₂ := b4e39 y y
               grind)
            | exact superpose b4e39 b4e272184
            | exact resolve b4e272184 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e272184
          have b4e272305 : (M.op (σ x) y) = (M.op y y) := by
            first
            | (have i₁ := b4e272234
               have i₂ := b4e127 y
               grind)
            | exact superpose b4e127 b4e272234
            | exact resolve b4e272234 b4e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e272234
          have b4e272407 : (M.op y y) = (M.op y x) := by
            first
            | (have i₁ := b4e9654
               have i₂ := b4e272123
               grind)
            | exact superpose b4e272123 b4e9654
            | exact resolve b4e9654 b4e272123
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9654
          have b4e272453 : (M.op y y) = (M.op (M.op y x) y) := by
            first
            | (have i₁ := b4e98634 y
               have i₂ := b4e272123
               grind)
            | exact superpose b4e272123 b4e98634
            | exact resolve b4e98634 b4e272123
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e98634 b4e272123
          have b4e272653 : (M.op y y) = (M.op y (M.op x y)) := by
            first
            | (have i₁ := b4e272453
               have i₂ := b4e108 x y
               grind)
            | exact superpose b4e108 b4e272453
            | exact resolve b4e272453 b4e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e272453
          have b4e272780 : (M.op y x) = (M.op y (M.op x y)) := by
            first
            | (have i₁ := b4e272653
               have i₂ := b4e272407
               grind)
            | exact superpose b4e272407 b4e272653
            | exact resolve b4e272653 b4e272407
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e272653
          have b4e273236 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op y x) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e44 y X0
               have i₂ := b4e272407
               grind)
            | exact superpose b4e272407 b4e44
            | exact resolve b4e44 b4e272407
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44
          have b4e273382 : (M.op y x) = (M.op y (M.op y x)) := by
            first
            | (have i₁ := b4e38 y y
               have i₂ := b4e272407
               grind)
            | exact superpose b4e272407 b4e38
            | exact resolve b4e38 b4e272407
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e273473 : (M.op x (σ y)) = (M.op y x) := by
            first
            | (have i₁ := b4e273382
               have i₂ := b4e39 y x
               grind)
            | exact superpose b4e39 b4e273382
            | exact resolve b4e273382 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39 b4e273382
          have b4e273583 : (M.op (σ y) (σ y)) = (M.op (M.op y x) y) := by
            first
            | (have i₁ := b4e273236 x
               have i₂ := b4e114 (M.op y x) x
               grind)
            | exact superpose b4e114 b4e273236
            | exact resolve b4e273236 b4e114
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e114 b4e273236
          have b4e273818 : (M.op x y) = (M.op y x) := by
            first
            | (have i₁ := b4e273473
               have i₂ := b4e45
               grind)
            | exact superpose b4e45 b4e273473
            | exact resolve b4e273473 b4e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45 b4e273473
          have b4e273899 : (M.op (σ y) (σ y)) = (M.op y (M.op x y)) := by
            first
            | (have i₁ := b4e273583
               have i₂ := b4e108 x y
               grind)
            | exact superpose b4e108 b4e273583
            | exact resolve b4e273583 b4e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e108 b4e273583
          have b4e274106 : (M.op (σ y) (σ y)) = (M.op y x) := by
            first
            | (have i₁ := b4e273899
               have i₂ := b4e272780
               grind)
            | exact superpose b4e272780 b4e273899
            | exact resolve b4e273899 b4e272780
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e272780 b4e273899
          have b4e274239 : (M.op x y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b4e274106
               have i₂ := b4e273818
               grind)
            | exact superpose b4e273818 b4e274106
            | exact resolve b4e274106 b4e273818
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e274106
          have b4e274336 : (M.op x y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e274239
               have i₂ := b4e97698 y
               grind)
            | exact superpose b4e97698 b4e274239
            | exact resolve b4e274239 b4e97698
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e97698 b4e274239
          have b4e274402 : (M.op x y) = (σ (M.op y x)) := by
            first
            | (have i₁ := b4e274336
               have i₂ := b4e272407
               grind)
            | exact superpose b4e272407 b4e274336
            | exact resolve b4e274336 b4e272407
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e274336
          have b4e274438 : (M.op x y) = (σ (M.op x y)) := by
            first
            | (have i₁ := b4e274402
               have i₂ := b4e273818
               grind)
            | exact superpose b4e273818 b4e274402
            | exact resolve b4e274402 b4e273818
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e274402
          have b4e277134 : (M.op y y) = (M.op (σ x) (M.op y y)) := by
            first
            | (have i₁ := b4e38 (σ x) y
               have i₂ := b4e272305
               grind)
            | exact superpose b4e272305 b4e38
            | exact resolve b4e38 b4e272305
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38 b4e272305
          have b4e277197 : (M.op (σ x) (σ y)) = (M.op y y) := by
            first
            | (have i₁ := b4e277134
               have i₂ := b4e33 y
               grind)
            | exact superpose b4e33 b4e277134
            | exact resolve b4e277134 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33 b4e277134
          have b4e277307 : (M.op (σ x) (σ y)) = (M.op y x) := by
            first
            | (have i₁ := b4e277197
               have i₂ := b4e272407
               grind)
            | exact superpose b4e272407 b4e277197
            | exact resolve b4e277197 b4e272407
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e272407 b4e277197
          have b4e277412 : (M.op x y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e277307
               have i₂ := b4e273818
               grind)
            | exact superpose b4e273818 b4e277307
            | exact resolve b4e277307 b4e273818
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e273818 b4e277307
          have b4e277482 : (M.op x y) = (M.op (σ x) y) := by
            first
            | (have i₁ := b4e277412
               have i₂ := b4e127 (σ x)
               grind)
            | exact superpose b4e127 b4e277412
            | exact resolve b4e277412 b4e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e127 b4e277412
          have b4e279635 : (M.op x y) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e184
               have i₂ := b4e274438
               grind)
            | exact superpose b4e274438 b4e184
            | exact resolve b4e184 b4e274438
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e184 b4e274438
          have b4e279802 : False := by grind
          exact b4e279802
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ (M.op x y) := by grind
          have b5e22 : y = (M.op x x) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e55 : x = (k x y) ∨ x = (M.op x y) := by grind
          have b5e60 : x = (k x y) := by
            first
            | (have r₁ := b5e55
               have r₂ := b5e21
               grind)
            | exact resolve b5e55 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55
          have b5e71 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e18 (σ x) X0
               grind)
            | (have i₁ := b5e24
               have i₂ := b5e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b5e18 b5e24
            | (have j1 := b5e18 (σ x) X0
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | exact resolve b5e24 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e87 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
            intro X0
            first
            | (have j0 := b5e71 X0
               have j1 := b5e16 (σ x) X0
               grind)
            | (have r₁ := b5e71 x
               have r₂ := b5e16 (σ x) x
               grind)
            | exact resolve b5e71 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e71
          have b5e594 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e87 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e87
          have b5e595 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e594
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e594
            | exact resolve b5e594 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e594
          have b5e596 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e595
               have i₂ := b5e60
               grind)
            | exact superpose b5e60 b5e595
            | exact resolve b5e595 b5e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e60 b5e595
          have b5e597 : False := by grind
          exact b5e597
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op x y) := by grind
        have b6e21 : y ≠ (M.op x x) := by grind
        have b6e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e39 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ y)
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
        have b6e42 : (σ x) = (k (σ x) (σ y)) := by grind
        clear b6e39
        have b6e43 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b6e42
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e42
          | exact resolve b6e42 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42
        have b6e46 : (k x y) = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e43
             grind)
          | exact superpose b6e43 b6e13
          | exact resolve b6e13 b6e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43
        have b6e47 : x = (k x y) := by
          first
          | (have i₁ := b6e46
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e46
          | exact resolve b6e46 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e46
        have b6e59 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e47
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e47
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e47 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e47
        have b6e67 : x = (M.op x y) ∨ y = (M.op x x) := by grind
        clear b6e59
        have b6e75 : y = (M.op x x) := by
          first
          | (have r₁ := b6e67
             have r₂ := b6e20
             grind)
          | exact resolve b6e67 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e67
        have b6e80 : False := by grind
        exact b6e80
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ (M.op x y) := by grind
          have b7e22 : y ≠ (M.op x x) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e69 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          have b7e74 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e69
               have r₂ := b7e23
               grind)
            | exact resolve b7e69 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69
          have b7e77 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e74
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e74
            | exact resolve b7e74 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e74
          have b7e83 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e77
               grind)
            | exact superpose b7e77 b7e14
            | exact resolve b7e14 b7e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77
          have b7e84 : x = (k x y) := by
            first
            | (have i₁ := b7e83
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e83
            | exact resolve b7e83 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83
          have b7e125 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e84
               grind)
            | exact superpose b7e84 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e84
          have b7e126 : x = (M.op x y) ∨ y = (M.op x x) := by grind
          clear b7e125
          have b7e128 : y = (M.op x x) := by
            first
            | (have r₁ := b7e126
               have r₂ := b7e21
               grind)
            | exact resolve b7e126 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e126
          have b7e130 : False := by grind
          exact b7e130
        · have b8e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op x y) := by grind
          have b8e22 : y ≠ (M.op x x) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e82 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 (σ x) X0
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b8e18 b8e24
            | (have j1 := b8e18 (σ x) X0
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e94 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
            intro X0
            first
            | (have j0 := b8e82 X0
               have j1 := b8e16 (σ x) X0
               grind)
            | (have r₁ := b8e82 x
               have r₂ := b8e16 (σ x) x
               grind)
            | exact resolve b8e82 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e82
          have b8e207 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e94 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e94
          have b8e208 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e207
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e207
            | exact resolve b8e207 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e207
          have b8e209 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e208
               grind)
            | exact superpose b8e208 b8e20
            | exact resolve b8e20 b8e208
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e208
          have b8e513 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e209
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e209
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e209 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e209
          have b8e514 : y = (M.op x x) ∨ x = (M.op x y) := by grind
          clear b8e513
          have b8e516 : x = (M.op x y) := by
            first
            | (have r₁ := b8e514
               have r₂ := b8e22
               grind)
            | exact resolve b8e514 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e514
          have b8e517 : False := by grind
          exact b8e517

/-- `Equation4403`: `x ◇ (x ◇ y) = (x ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(X,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_y_pyx_pxx_pyx_Equation4403 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4403 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4403.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (M.op x y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op x x) (M.op x x) with h2a | h2a
      · have b0e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b0e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : (M.op x y) = (M.op x x) := by grind
        have b0e21 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e23 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e21
             grind)
          | exact superpose b0e21 b0e19
          | exact resolve b0e19 b0e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e24 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b0e23
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e23
          | exact resolve b0e23 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e23
        have b0e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b0e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b0e18 X0 X0
             have i₂ := b0e51 (σ X0)
             grind)
          | exact superpose b0e51 b0e18
          | exact resolve b0e18 b0e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e62 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b0e57 X0
             have i₂ := b0e51 X0
             grind)
          | exact superpose b0e51 b0e57
          | exact resolve b0e57 b0e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e51 b0e57
        have b0e230 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b0e24
             have i₂ := b0e62 x
             grind)
          | exact superpose b0e62 b0e24
          | (have r₁ := b0e24
             have r₂ := b0e62 x
             grind)
          | exact resolve b0e24 b0e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e24 b0e62
        have b0e241 : False := by grind
        exact b0e241
      · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
        · have b1e23 : (M.op x x) ≠ (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e25 : False := by grind
          exact b1e25
        · have b2e23 : (M.op x x) ≠ (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e25 : False := by grind
          exact b2e25
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · rcases eq_or_ne (M.op x x) (M.op x x) with h2a | h2a
        · have b3e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X2) := by
            intro X0 X1 X2
            grind
          have b3e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b3e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b3e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b3e21 : (M.op x y) = (M.op x x) := by grind
          have b3e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b3e23 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e25 : (σ y) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b3e22
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e22
            | exact resolve b3e22 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e26 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b3e20
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e20
            | exact resolve b3e20 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e27 : (σ y) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b3e26
               have i₂ := b3e21
               grind)
            | exact superpose b3e21 b3e26
            | exact resolve b3e26 b3e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e26
          have b3e30 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) X3) = (M.op X0 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b3e13 X0 (M.op X0 x) X3
               have i₂ := b3e13 X0 x X1
               grind)
            | exact superpose b3e13 b3e13
            | exact resolve b3e13 b3e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e32 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) X0) X0) := by
            intro X0
            first
            | (have i₁ := b3e13 (σ x) (σ y) X0
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e13
            | exact resolve b3e13 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e33 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X3) X3) := by
            intro X0 X1 X3
            first
            | (have i₁ := b3e13 X0 x X3
               have i₂ := b3e13 X0 x X1
               grind)
            | exact superpose b3e13 b3e13
            | exact resolve b3e13 b3e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e39 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) X0) := by
            intro X0
            first
            | (have i₁ := b3e32 X0
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e32
            | exact resolve b3e32 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e32
          have b3e40 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b3e39 (σ y)
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e39
            | exact resolve b3e39 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e39
          have b3e49 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y x) := by
            first
            | (have i₁ := b3e16 x y
               have i₂ := b3e21
               grind)
            | exact superpose b3e21 b3e16
            | (have j0 := b3e16 x x
               grind)
            | (have r₁ := b3e16 x y
               have r₂ := b3e21
               grind)
            | exact resolve b3e16 b3e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e50 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b3e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e51 : (k x y) = (M.op y x) := by grind
          clear b3e49
          have b3e53 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b3e19 X0 X0
               have i₂ := b3e50 (σ X0)
               grind)
            | exact superpose b3e50 b3e19
            | exact resolve b3e19 b3e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e54 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b3e53 X0
               have i₂ := b3e50 X0
               grind)
            | exact superpose b3e50 b3e53
            | exact resolve b3e53 b3e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e53
          have b3e59 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b3e17 (σ x) (σ y)
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e17
            | (have j0 := b3e17 (σ x) (σ y)
               grind)
            | (have r₁ := b3e17 (σ x) (σ y)
               have r₂ := b3e23
               grind)
            | exact resolve b3e17 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e60 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b3e59
          have b3e61 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b3e60
               have r₂ := b3e25
               grind)
            | exact resolve b3e60 b3e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e25 b3e60
          have b3e62 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b3e61
               have i₂ := b3e19 x y
               grind)
            | exact superpose b3e19 b3e61
            | exact resolve b3e61 b3e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e61
          have b3e63 : (M.op (σ x) (σ x)) = (σ (M.op y x)) := by
            first
            | (have i₁ := b3e62
               have i₂ := b3e51
               grind)
            | exact superpose b3e51 b3e62
            | exact resolve b3e62 b3e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e51 b3e62
          have b3e64 : (σ (M.op x x)) = (σ (M.op y x)) := by
            first
            | (have i₁ := b3e63
               have i₂ := b3e54 x
               grind)
            | exact superpose b3e54 b3e63
            | exact resolve b3e63 b3e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e54 b3e63
          have b3e87 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b3e16 (σ y) (σ y)
               have i₂ := b3e40
               grind)
            | exact superpose b3e40 b3e16
            | exact resolve b3e16 b3e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e40
          have b3e92 : (σ y) = (k (σ y) (σ y)) := by grind
          clear b3e87
          have b3e95 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b3e92
               have i₂ := b3e19 y y
               grind)
            | exact superpose b3e19 b3e92
            | exact resolve b3e92 b3e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e92
          have b3e96 : (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b3e95
               have i₂ := b3e50 y
               grind)
            | exact superpose b3e50 b3e95
            | exact resolve b3e95 b3e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e50 b3e95
          have b3e99 : (M.op y x) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b3e14 (M.op y x)
               have i₂ := b3e64
               grind)
            | exact superpose b3e64 b3e14
            | exact resolve b3e14 b3e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e64
          have b3e100 : (M.op x x) = (M.op y x) := by
            first
            | (have i₁ := b3e99
               have i₂ := b3e14 (M.op x x)
               grind)
            | exact superpose b3e14 b3e99
            | exact resolve b3e99 b3e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e99
          have b3e115 : (M.op y y) = (τ (σ y)) := by
            first
            | (have i₁ := b3e14 (M.op y y)
               have i₂ := b3e96
               grind)
            | exact superpose b3e96 b3e14
            | exact resolve b3e14 b3e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e96
          have b3e116 : y = (M.op y y) := by
            first
            | (have i₁ := b3e115
               have i₂ := b3e14 y
               grind)
            | exact superpose b3e14 b3e115
            | exact resolve b3e115 b3e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e115
          have b3e164 : ∀ X0 : G, (M.op y y) = (M.op (M.op y X0) X0) := by
            intro X0
            first
            | (have i₁ := b3e33 y X0 y
               have i₂ := b3e116
               grind)
            | exact superpose b3e116 b3e33
            | exact resolve b3e33 b3e116
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e179 : ∀ X0 : G, y = (M.op (M.op y X0) X0) := by
            intro X0
            first
            | (have i₁ := b3e164 X0
               have i₂ := b3e116
               grind)
            | exact superpose b3e116 b3e164
            | exact resolve b3e164 b3e116
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e116 b3e164
          have b3e215 : y = (M.op (M.op x x) x) := by
            first
            | (have i₁ := b3e179 x
               have i₂ := b3e100
               grind)
            | exact superpose b3e100 b3e179
            | exact resolve b3e179 b3e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e100 b3e179
          have b3e350 : ∀ X0 : G, y = (M.op (M.op x X0) X0) := by
            intro X0
            first
            | (have i₁ := b3e33 x x X0
               have i₂ := b3e215
               grind)
            | exact superpose b3e215 b3e33
            | exact resolve b3e33 b3e215
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e33
          have b3e409 : ∀ X0 : G, (M.op x y) = (M.op (M.op x X0) X0) := by
            intro X0
            first
            | (have i₁ := b3e30 x x X0
               have i₂ := b3e215
               grind)
            | exact superpose b3e215 b3e30
            | exact resolve b3e30 b3e215
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e30 b3e215
          have b3e441 : y = (M.op x y) := by
            first
            | (have i₁ := b3e409 x
               have i₂ := b3e350 x
               grind)
            | exact superpose b3e350 b3e409
            | exact resolve b3e409 b3e350
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e350 b3e409
          have b3e467 : y = (M.op x x) := by
            first
            | (have i₁ := b3e21
               have i₂ := b3e441
               grind)
            | exact superpose b3e441 b3e21
            | exact resolve b3e21 b3e441
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e441
          have b3e546 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b3e27
               have i₂ := b3e467
               grind)
            | exact superpose b3e467 b3e27
            | exact resolve b3e27 b3e467
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e27 b3e467
          have b3e557 : False := by grind
          exact b3e557
        · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
          · have b4e25 : (M.op x x) ≠ (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e27 : False := by grind
            exact b4e27
          · have b5e25 : (M.op x x) ≠ (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e27 : False := by grind
            exact b5e27
      · rcases eq_or_ne (M.op x x) (M.op x x) with h2a | h2a
        · have b6e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X2) := by
            intro X0 X1 X2
            grind
          have b6e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b6e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b6e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b6e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b6e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b6e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b6e21 : (M.op x y) = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e25 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b6e20
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e20
            | exact resolve b6e20 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e26 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b6e19 (τ X0) X1
               have i₂ := b6e15 X0
               grind)
            | exact superpose b6e15 b6e19
            | exact resolve b6e19 b6e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b6e19 X1 (τ X0)
               have i₂ := b6e15 X0
               grind)
            | exact superpose b6e15 b6e19
            | exact resolve b6e19 b6e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e32 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) X3) = (M.op X0 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b6e13 X0 (M.op X0 x) X3
               have i₂ := b6e13 X0 x X1
               grind)
            | exact superpose b6e13 b6e13
            | exact resolve b6e13 b6e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X2) X3) X3) = (M.op (M.op X0 X2) (M.op X0 (M.op X0 X1))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b6e13 (M.op X0 X2) X2 X3
               have i₂ := b6e13 X0 X1 X2
               grind)
            | exact superpose b6e13 b6e13
            | exact resolve b6e13 b6e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e34 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X3) X3) := by
            intro X0 X1 X3
            first
            | (have i₁ := b6e13 X0 x X3
               have i₂ := b6e13 X0 x X1
               grind)
            | exact superpose b6e13 b6e13
            | exact resolve b6e13 b6e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e35 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op (M.op x x) y) := by
            intro X0
            first
            | (have i₁ := b6e13 x X0 y
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e13
            | exact resolve b6e13 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e37 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op (M.op X0 X2) X3)) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b6e13 (M.op X0 X2) X3 X2
               have i₂ := b6e13 X0 X1 X2
               grind)
            | exact superpose b6e13 b6e13
            | exact resolve b6e13 b6e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e38 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b6e13 X0 X1 x
               have i₂ := b6e13 X0 X2 x
               grind)
            | exact superpose b6e13 b6e13
            | exact resolve b6e13 b6e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e44 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b6e14 (k X0 (τ X1))
               have i₂ := b6e27 X1 X0
               grind)
            | exact superpose b6e27 b6e14
            | exact resolve b6e14 b6e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b6e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e60 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b6e19 X0 X0
               have i₂ := b6e57 (σ X0)
               grind)
            | exact superpose b6e57 b6e19
            | exact resolve b6e19 b6e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e62 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
            intro X0
            first
            | (have i₁ := b6e27 X0 (τ X0)
               have i₂ := b6e57 (τ X0)
               grind)
            | exact superpose b6e57 b6e27
            | exact resolve b6e27 b6e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e65 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b6e62 X0
               have i₂ := b6e15 X0
               grind)
            | exact superpose b6e15 b6e62
            | exact resolve b6e62 b6e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e62
          have b6e67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b6e60 X0
               have i₂ := b6e57 X0
               grind)
            | exact superpose b6e57 b6e60
            | exact resolve b6e60 b6e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e60
          have b6e70 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b6e65 X0
               have i₂ := b6e57 X0
               grind)
            | exact superpose b6e57 b6e65
            | exact resolve b6e65 b6e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e57 b6e65
          have b6e79 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b6e19 X1 X0
               have i₂ := b6e18 (σ X1) (σ X0)
               grind)
            | exact superpose b6e18 b6e19
            | (have j1 := b6e18 (σ X1) (σ X0)
               grind)
            | exact resolve b6e19 b6e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e81 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b6e16 X0 X1
               have i₂ := b6e18 X0 X1
               grind)
            | (have i₁ := b6e16 X0 X0
               have i₂ := b6e18 X0 X1
               grind)
            | exact superpose b6e18 b6e16
            | (have j0 := b6e16 X0 X0
               have j1 := b6e18 X0 X1
               grind)
            | (have r₁ := b6e16 X0 X1
               have r₂ := b6e18 X0 X1
               grind)
            | (have r₁ := b6e16 X1 X1
               have r₂ := b6e18 X1 X1
               grind)
            | (have r₁ := b6e16 X0 (M.op X0 X0)
               have r₂ := b6e18 X0 (M.op X0 X0)
               grind)
            | exact resolve b6e16 b6e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e88 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b6e18 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e90 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b6e81 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e81
          have b6e91 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b6e90 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e90
          have b6e93 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b6e79 X0 X1
               have i₂ := b6e67 X1
               grind)
            | exact superpose b6e67 b6e79
            | (have j0 := b6e79 X0 X1
               grind)
            | exact resolve b6e79 b6e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e79
          have b6e123 : ∀ X0 : G, (M.op (M.op x X0) X0) = (M.op (M.op x x) y) := by
            intro X0
            first
            | (have i₁ := b6e34 x X0 y
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e34
            | exact resolve b6e34 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e145 : ∀ X0 X1 : G, (M.op (M.op (σ X0) X1) X1) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b6e13 (σ X0) (σ X0) X1
               have i₂ := b6e67 X0
               grind)
            | exact superpose b6e67 b6e13
            | exact resolve b6e13 b6e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e146 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) X1)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b6e13 (σ X0) X1 (σ X0)
               have i₂ := b6e67 X0
               grind)
            | exact superpose b6e67 b6e13
            | exact resolve b6e13 b6e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e149 : ∀ X0 X1 : G, (M.op (M.op (σ X0) X1) X1) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b6e34 (σ X0) X1 (σ X0)
               have i₂ := b6e67 X0
               grind)
            | exact superpose b6e67 b6e34
            | exact resolve b6e34 b6e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e151 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b6e16 (σ X0) X1
               have i₂ := b6e67 X0
               grind)
            | exact superpose b6e67 b6e16
            | (have j0 := b6e16 (σ X0) X1
               grind)
            | exact resolve b6e16 b6e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e156 : (M.op (M.op x x) y) = (M.op x (M.op (M.op x x) y)) := by
            first
            | (have i₁ := b6e35 (M.op x x)
               have i₂ := b6e35 x
               grind)
            | exact superpose b6e35 b6e35
            | exact resolve b6e35 b6e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e229 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X2)) = (M.op (M.op X0 (M.op X0 X1)) (M.op X0 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b6e13 X0 X2 (M.op X0 X3)
               have i₂ := b6e38 X0 X3 X1
               grind)
            | (have i₁ := b6e13 X0 X2 (M.op X0 X3)
               have i₂ := b6e38 X0 X1 X3
               grind)
            | exact superpose b6e38 b6e13
            | exact resolve b6e13 b6e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e230 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 X0) ∨ (k X0 (M.op X0 X2)) = (M.op (M.op X0 X2) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b6e16 X0 (M.op X0 X2)
               have i₂ := b6e38 X0 X2 X1
               grind)
            | (have i₁ := b6e16 X0 (M.op X0 X2)
               have i₂ := b6e38 X0 X1 X2
               grind)
            | exact superpose b6e38 b6e16
            | (have j0 := b6e16 X0 (M.op X0 X1)
               grind)
            | exact resolve b6e16 b6e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e258 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b6e19 X1 X0
               have i₂ := b6e91 (σ X1) (σ X0)
               grind)
            | exact superpose b6e91 b6e19
            | (have j1 := b6e91 (σ X1) (σ X0)
               grind)
            | exact resolve b6e19 b6e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e260 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b6e26 X1 X0
               have i₂ := b6e91 (τ X1) X0
               grind)
            | exact superpose b6e91 b6e26
            | (have j1 := b6e91 (τ X1) X0
               grind)
            | exact resolve b6e26 b6e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e91
          have b6e282 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X0 X2)) = (M.op X0 (M.op (M.op X0 X3) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b6e32 X0 X3 (M.op X0 X2)
               have i₂ := b6e38 X0 X2 X1
               grind)
            | (have i₁ := b6e32 X0 X3 (M.op X0 X2)
               have i₂ := b6e38 X0 X1 X2
               grind)
            | exact superpose b6e38 b6e32
            | exact resolve b6e32 b6e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e294 : ∀ X0 X1 X3 : G, (M.op X0 (M.op (M.op X0 X1) X1)) = (M.op X0 (M.op (M.op X0 X3) X3)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b6e32 X0 X3 x
               have i₂ := b6e32 X0 X1 x
               grind)
            | exact superpose b6e32 b6e32
            | exact resolve b6e32 b6e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e299 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X2) = (M.op X0 (M.op (M.op X0 (M.op X0 X1)) (M.op X0 X3))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b6e32 X0 (M.op X0 X3) X2
               have i₂ := b6e38 X0 X3 X1
               grind)
            | (have i₁ := b6e32 X0 (M.op X0 X3) X2
               have i₂ := b6e38 X0 X1 X3
               grind)
            | exact superpose b6e38 b6e32
            | exact resolve b6e32 b6e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e325 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X2) X3) X3) = (M.op (M.op X0 (M.op (M.op X0 X1) X1)) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b6e34 (M.op X0 X2) X3 X2
               have i₂ := b6e32 X0 X1 X2
               grind)
            | exact superpose b6e32 b6e34
            | exact resolve b6e34 b6e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e32
          have b6e341 : ∀ X0 X1 : G, (M.op (M.op x x) y) = (M.op (M.op x (M.op x X0)) (M.op x X1)) := by
            intro X0 X1
            first
            | (have i₁ := b6e123 (M.op x X1)
               have i₂ := b6e38 x X1 X0
               grind)
            | (have i₁ := b6e123 (M.op x X1)
               have i₂ := b6e38 x X0 X1
               grind)
            | exact superpose b6e38 b6e123
            | exact resolve b6e123 b6e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e356 : ∀ X0 X1 : G, (M.op (M.op x X0) (M.op (M.op x X0) X1)) = (M.op (M.op (M.op x x) y) X0) := by
            intro X0 X1
            first
            | (have i₁ := b6e13 (M.op x X0) X1 X0
               have i₂ := b6e123 X0
               grind)
            | exact superpose b6e123 b6e13
            | exact resolve b6e13 b6e123
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e488 : (M.op (M.op x x) y) = (M.op (M.op (M.op x x) y) (M.op (M.op x x) y)) := by
            first
            | (have i₁ := b6e123 (M.op (M.op x x) y)
               have i₂ := b6e156
               grind)
            | exact superpose b6e156 b6e123
            | exact resolve b6e123 b6e156
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e156
          have b6e712 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x x) y) (M.op (M.op (M.op x x) y) X1)) = (M.op (M.op x (M.op x X2)) (M.op x X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b6e37 x X1 (M.op x X0) x
               have i₂ := b6e35 X0
               grind)
            | exact superpose b6e35 b6e37
            | exact resolve b6e37 b6e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e746 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x X0) X1) (M.op (M.op (M.op x X0) X1) X2)) = (M.op (M.op (M.op x X0) (M.op (M.op x x) y)) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b6e37 (M.op x X0) X0 X1 X2
               have i₂ := b6e123 X0
               grind)
            | exact superpose b6e123 b6e37
            | exact resolve b6e37 b6e123
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e37 b6e123
          have b6e815 : ∀ X1 : G, (M.op (M.op x x) y) = (M.op (M.op (M.op x x) y) (M.op (M.op (M.op x x) y) X1)) := by
            intro X1
            first
            | (have i₁ := b6e712 x X1 x
               have i₂ := b6e341 x x
               grind)
            | exact superpose b6e341 b6e712
            | exact resolve b6e712 b6e341
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e341 b6e712
          have b6e822 : (M.op (M.op x x) y) = (M.op (M.op (M.op x x) (M.op (M.op x x) y)) y) := by
            first
            | (have i₁ := b6e815 x
               have i₂ := b6e746 x y x
               grind)
            | exact superpose b6e746 b6e815
            | exact resolve b6e815 b6e746
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e746 b6e815
          have b6e826 : (M.op (M.op x x) y) = (M.op (M.op (M.op (M.op x x) y) x) y) := by
            first
            | (have i₁ := b6e822
               have i₂ := b6e356 x y
               grind)
            | exact superpose b6e356 b6e822
            | exact resolve b6e822 b6e356
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e356 b6e822
          have b6e944 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
            intro X0
            first
            | (have j0 := b6e88 X0 (M.op X0 X0)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e88
          have b6e945 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
            intro X0
            first
            | (have j0 := b6e944 X0
               have j1 := b6e230 X0 x X0
               grind)
            | (have r₁ := b6e944 x
               have r₂ := b6e230 x x x
               grind)
            | exact resolve b6e944 b6e230
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e230 b6e944
          have b6e948 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ X0) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b6e945 (σ X0)
               have i₂ := b6e67 X0
               grind)
            | exact superpose b6e67 b6e945
            | exact resolve b6e945 b6e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e955 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k X0 (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b6e948 X0
               have i₂ := b6e19 X0 (M.op X0 X0)
               grind)
            | exact superpose b6e19 b6e948
            | exact resolve b6e948 b6e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e948
          have b6e959 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
            intro X0
            first
            | (have i₁ := b6e955 X0
               have i₂ := b6e945 X0
               grind)
            | exact superpose b6e945 b6e955
            | exact resolve b6e955 b6e945
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e945 b6e955
          have b6e1636 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b6e145 X0 (σ X0)
               have i₂ := b6e67 X0
               grind)
            | exact superpose b6e67 b6e145
            | exact resolve b6e145 b6e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e1641 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (M.op (σ X0) (M.op (σ X0) X1)) (M.op (σ X0) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b6e145 X0 (M.op (σ X0) X2)
               have i₂ := b6e38 (σ X0) X2 X1
               grind)
            | (have i₁ := b6e145 X0 (M.op (σ X0) X2)
               have i₂ := b6e38 (σ X0) X1 X2
               grind)
            | exact superpose b6e38 b6e145
            | exact resolve b6e145 b6e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e38
          have b6e1679 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (M.op (M.op (σ X0) (M.op (σ X0) (M.op (σ X0) X1))) X2) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b6e33 (σ X0) X1 (M.op (σ X0) (M.op (σ X0) X1)) X2
               have i₂ := b6e145 X0 (M.op (σ X0) (M.op (σ X0) X1))
               grind)
            | exact superpose b6e145 b6e33
            | exact resolve b6e33 b6e145
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e145
          have b6e1730 : ∀ X0 X2 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (M.op (M.op (σ (M.op X0 X0)) (σ X0)) X2) X2) := by
            intro X0 X2
            first
            | (have i₁ := b6e1679 X0 x X2
               have i₂ := b6e146 X0 (M.op (σ X0) x)
               grind)
            | exact superpose b6e146 b6e1679
            | exact resolve b6e1679 b6e146
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1679
          have b6e1739 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) X0)) := by
            intro X0
            first
            | (have i₁ := b6e1636 X0
               have i₂ := b6e959 X0
               grind)
            | exact superpose b6e959 b6e1636
            | exact resolve b6e1636 b6e959
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1636
          have b6e1743 : ∀ X0 X2 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (M.op (σ (M.op (M.op X0 X0) X0)) X2) X2) := by
            intro X0 X2
            first
            | (have i₁ := b6e1730 X0 X2
               have i₂ := b6e959 X0
               grind)
            | exact superpose b6e959 b6e1730
            | exact resolve b6e1730 b6e959
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1730
          have b6e1748 : ∀ X0 X2 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (M.op (σ (M.op (M.op X0 X0) X0)) X2) X2) := by
            intro X0 X2
            first
            | (have i₁ := b6e1743 X0 X2
               have i₂ := b6e1739 X0
               grind)
            | exact superpose b6e1739 b6e1743
            | exact resolve b6e1743 b6e1739
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1743
          have b6e2142 : ∀ X0 X1 : G, (M.op (M.op (σ X0) X1) X1) = (σ (M.op (M.op X0 X0) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b6e149 X0 X1
               have i₂ := b6e959 X0
               grind)
            | exact superpose b6e959 b6e149
            | exact resolve b6e149 b6e959
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e149
          have b6e2333 : ∀ X0 X1 X2 : G, (M.op (σ X1) (σ X0)) = (M.op (M.op (σ X1) X2) X2) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b6e13 (σ X1) (σ X0) X2
               have i₂ := b6e93 X0 X1
               grind)
            | exact superpose b6e93 b6e13
            | (have j1 := b6e93 X0 X1
               grind)
            | exact resolve b6e13 b6e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e2335 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b6e16 (σ X1) (σ X0)
               have i₂ := b6e93 X0 X1
               grind)
            | exact superpose b6e93 b6e16
            | (have j0 := b6e16 (σ X1) (σ X0)
               have j1 := b6e93 X0 X1
               grind)
            | exact resolve b6e16 b6e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e93
          have b6e2378 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b6e2335 X0 X1
               have j1 := b6e151 X1 (σ X0)
               grind)
            | (have r₁ := b6e2335 X0 X0
               have r₂ := b6e151 X0 (σ X0)
               grind)
            | exact resolve b6e2335 b6e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e2335
          have b6e2419 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X1 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b6e2378 X0 X1
               have i₂ := b6e67 X1
               grind)
            | exact superpose b6e67 b6e2378
            | (have j0 := b6e2378 X0 X1
               grind)
            | (have r₁ := b6e2378 (M.op X0 X0) X0
               have r₂ := b6e67 X0
               grind)
            | exact resolve b6e2378 b6e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e2378
          have b6e2441 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b6e2419 X0 X1
               have i₂ := b6e19 X1 X0
               grind)
            | exact superpose b6e19 b6e2419
            | (have j0 := b6e2419 X0 X1
               grind)
            | exact resolve b6e2419 b6e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e2419
          have b6e2442 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b6e2441 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e2441
          have b6e2494 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) X2) X2) = (σ (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b6e2142 X0 X2
               have i₂ := b6e34 X0 X0 X1
               grind)
            | (have i₁ := b6e2142 X0 X2
               have i₂ := b6e34 X0 X1 X0
               grind)
            | exact superpose b6e34 b6e2142
            | exact resolve b6e2142 b6e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e34
          have b6e2495 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) X2) X2) = (σ (M.op X0 (M.op X0 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b6e2142 X0 X2
               have i₂ := b6e13 X0 X1 X0
               grind)
            | exact superpose b6e13 b6e2142
            | exact resolve b6e2142 b6e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e2653 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (σ (M.op (M.op (τ X0) X2) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b6e2494 (τ X0) X2 X1
               have i₂ := b6e15 X0
               grind)
            | exact superpose b6e15 b6e2494
            | exact resolve b6e2494 b6e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e2706 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (σ (M.op X0 X2)) X3) X3) = (σ (M.op (M.op X0 (M.op X0 X1)) X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b6e2494 (M.op X0 X2) X2 X3
               have i₂ := b6e13 X0 X1 X2
               grind)
            | exact superpose b6e13 b6e2494
            | exact resolve b6e2494 b6e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e2494
          have b6e2990 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 (M.op X0 X1))) = (M.op (M.op (M.op (σ X0) (M.op (σ X0) (M.op (σ X0) X2))) X3) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b6e33 (σ X0) X2 (M.op (σ X0) (M.op (σ X0) X2)) X3
               have i₂ := b6e2495 X0 X1 (M.op (σ X0) (M.op (σ X0) X2))
               grind)
            | exact superpose b6e2495 b6e33
            | exact resolve b6e33 b6e2495
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e33
          have b6e3019 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X2)) = (τ (M.op (M.op (σ X0) X1) X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b6e14 (M.op X0 (M.op X0 X2))
               have i₂ := b6e2495 X0 X2 X1
               grind)
            | exact superpose b6e2495 b6e14
            | exact resolve b6e14 b6e2495
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e3038 : ∀ X0 X1 X3 : G, (σ (M.op X0 (M.op X0 X1))) = (M.op (M.op (M.op (σ (M.op X0 X0)) (σ X0)) X3) X3) := by
            intro X0 X1 X3
            first
            | (have i₁ := b6e2990 X0 X1 x X3
               have i₂ := b6e146 X0 (M.op (σ X0) x)
               grind)
            | exact superpose b6e146 b6e2990
            | exact resolve b6e2990 b6e146
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e146 b6e2990
          have b6e3054 : ∀ X0 X1 X3 : G, (σ (M.op X0 (M.op X0 X1))) = (M.op (M.op (σ (M.op (M.op X0 X0) X0)) X3) X3) := by
            intro X0 X1 X3
            first
            | (have i₁ := b6e3038 X0 X1 X3
               have i₂ := b6e959 X0
               grind)
            | exact superpose b6e959 b6e3038
            | exact resolve b6e3038 b6e959
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e959 b6e3038
          have b6e3437 : ∀ X0 X1 X2 : G, (M.op (M.op (τ X0) X2) X2) = (τ (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b6e14 (M.op (M.op (τ X0) X2) X2)
               have i₂ := b6e2653 X0 X1 X2
               grind)
            | exact superpose b6e2653 b6e14
            | exact resolve b6e14 b6e2653
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e2653
          have b6e8300 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X2)) = (τ (M.op (σ X0) (M.op (σ X0) X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b6e3019 X0 (M.op (σ X0) x) X2
               have i₂ := b6e229 (σ X0) x X1 x
               grind)
            | exact superpose b6e229 b6e3019
            | exact resolve b6e3019 b6e229
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e229
          have b6e9476 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X2)) = (M.op (M.op X0 (M.op (M.op X0 X1) X1)) (M.op (M.op X0 X3) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b6e13 X0 X2 (M.op (M.op X0 X3) X3)
               have i₂ := b6e294 X0 X3 X1
               grind)
            | (have i₁ := b6e13 X0 X2 (M.op (M.op X0 X3) X3)
               have i₂ := b6e294 X0 X1 X3
               grind)
            | exact superpose b6e294 b6e13
            | exact resolve b6e13 b6e294
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e294
          have b6e13066 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op (M.op (M.op x (M.op x X0)) x) y) := by
            intro X0
            first
            | (have i₁ := b6e826
               have i₂ := b6e35 X0
               grind)
            | exact superpose b6e35 b6e826
            | exact resolve b6e826 b6e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e35 b6e826
          have b6e13495 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b6e260 X0 (σ X0)
               have i₂ := b6e14 X0
               grind)
            | exact superpose b6e14 b6e260
            | exact resolve b6e260 b6e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e260
          have b6e13623 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b6e13495 X0 X1
               have i₂ := b6e19 X0 X1
               grind)
            | exact superpose b6e19 b6e13495
            | (have j0 := b6e13495 X0 X1
               grind)
            | exact resolve b6e13495 b6e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e13495
          have b6e16375 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ (M.op (M.op X0 X0) X0))) = (M.op (M.op (σ X0) (M.op (σ X0) X1)) (M.op (σ X0) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b6e282 (σ X0) X1 X2 x
               have i₂ := b6e2142 X0 x
               grind)
            | exact superpose b6e2142 b6e282
            | exact resolve b6e282 b6e2142
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e282 b6e2142
          have b6e16720 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op (M.op X0 X0) X0))) := by
            intro X0
            first
            | (have i₁ := b6e16375 X0 x x
               have i₂ := b6e1641 X0 x x
               grind)
            | exact superpose b6e1641 b6e16375
            | exact resolve b6e16375 b6e1641
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1641 b6e16375
          have b6e16823 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op (M.op X0 X0) X0))) := by
            intro X0
            first
            | (have i₁ := b6e16720 X0
               have i₂ := b6e1739 X0
               grind)
            | exact superpose b6e1739 b6e16720
            | exact resolve b6e16720 b6e1739
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1739 b6e16720
          have b6e21735 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (M.op X0 X0)) X1) X1) = (M.op (M.op (σ X0) (M.op (M.op (σ X0) X2) X2)) (σ X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b6e325 (σ X0) X2 (σ X0) X1
               have i₂ := b6e67 X0
               grind)
            | exact superpose b6e67 b6e325
            | exact resolve b6e325 b6e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e325
          have b6e38311 : ∀ X0 X1 : G, (σ (M.op X1 X1)) ≠ X0 ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b6e2442 (τ X0) X1
               have i₂ := b6e15 X0
               grind)
            | exact superpose b6e15 b6e2442
            | (have r₁ := b6e2442 (τ (σ (M.op X1 X1))) X1
               have r₂ := b6e15 (σ (M.op X1 X1))
               grind)
            | exact resolve b6e2442 b6e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e38400 : ∀ X0 X1 : G, (σ (M.op X1 X1)) ≠ X0 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b6e38311 X0 X1
               have i₂ := b6e27 X0 X1
               grind)
            | exact superpose b6e27 b6e38311
            | (have j0 := b6e38311 X0 X1
               grind)
            | exact resolve b6e38311 b6e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e27 b6e38311
          have b6e273968 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k (σ (τ X0)) X1) = (M.op X1 (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b6e38400 X1 (τ X0)
               have i₂ := b6e70 X0
               grind)
            | exact superpose b6e70 b6e38400
            | (have j0 := b6e38400 X1 (τ X0)
               grind)
            | (have r₁ := b6e38400 (M.op X0 X0) (τ X0)
               have r₂ := b6e70 X0
               grind)
            | exact resolve b6e38400 b6e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e70 b6e38400
          have b6e273973 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b6e273968 X0 X1
               have i₂ := b6e15 X0
               grind)
            | exact superpose b6e15 b6e273968
            | (have j0 := b6e273968 X0 X1
               grind)
            | (have r₁ := b6e273968 X0 (σ (τ (M.op X0 X0)))
               have r₂ := b6e15 (M.op X0 X0)
               grind)
            | exact resolve b6e273968 b6e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e273968
          have b6e568312 : ∀ X0 X1 X2 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (M.op (σ X1) X2) X2) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b6e2333 X0 X1 X2
               have i₂ := b6e258 X0 X1
               grind)
            | exact superpose b6e258 b6e2333
            | (have j0 := b6e2333 X0 X1 X2
               have j1 := b6e258 X0 X1
               grind)
            | exact resolve b6e2333 b6e258
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e2333
          have b6e570437 : ∀ X0 X1 X2 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (M.op (σ X1) X2) X2) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1 X2
            first
            | (have j0 := b6e568312 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e568312
          have b6e570442 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ X1) X2) X2) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1 X2
            first
            | (have j0 := b6e570437 X0 X1 X2
               have j1 := b6e2442 X0 X1
               grind)
            | (have r₁ := b6e570437 X0 X1 X2
               have r₂ := b6e2442 X0 X1
               grind)
            | (have r₁ := b6e570437 (M.op X1 X1) X1 X2
               have r₂ := b6e2442 (M.op X1 X1) X1
               grind)
            | exact resolve b6e570437 b6e2442
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e570437
          have b6e956346 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (M.op (M.op X0 X2) X2) = (σ X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b6e570442 X0 (τ X0) X2
               have i₂ := b6e15 X0
               grind)
            | exact superpose b6e15 b6e570442
            | exact resolve b6e570442 b6e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e956364 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (M.op X0 X2) X2) = (σ X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b6e956346 X0 X1 X2
               have i₂ := b6e26 X0 X1
               grind)
            | exact superpose b6e26 b6e956346
            | (have j0 := b6e956346 X0 X1 X2
               grind)
            | exact resolve b6e956346 b6e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e956346
          have b6e956388 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X2) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b6e956364 X0 (τ X0) X2
               have i₂ := b6e15 X0
               grind)
            | exact superpose b6e15 b6e956364
            | exact resolve b6e956364 b6e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e956364
          have b6e956527 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ X0) X2) X2) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b6e1748 X2 X2
               have i₂ := b6e956388 X0 X2 X2
               grind)
            | (have i₁ := b6e1748 X0 X2
               have i₂ := b6e956388 (M.op (M.op X0 X0) X0) X1 X2
               grind)
            | exact superpose b6e956388 b6e1748
            | (have j1 := b6e956388 (σ X0) (σ X0) X2
               grind)
            | exact resolve b6e1748 b6e956388
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1748
          have b6e956773 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X2) X2) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b6e299 X1 x X2 x
               have i₂ := b6e956388 X0 X1 (M.op X1 x)
               grind)
            | (have i₁ := b6e299 X0 X1 X2 x
               have i₂ := b6e956388 (M.op (M.op X0 (M.op X0 X1)) (M.op X0 x)) X1 X2
               grind)
            | exact superpose b6e956388 b6e299
            | (have j1 := b6e956388 (M.op X1 X0) X1 X2
               grind)
            | exact resolve b6e299 b6e956388
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e299
          have b6e956795 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b6e9476 X1 x X2 x
               have i₂ := b6e956388 X0 X1 (M.op (M.op X1 x) x)
               grind)
            | (have i₁ := b6e9476 X0 X1 X2 x
               have i₂ := b6e956388 (M.op (M.op X0 (M.op (M.op X0 X1) X1)) (M.op (M.op X0 x) x)) X1 X2
               grind)
            | exact superpose b6e956388 b6e9476
            | (have j1 := b6e956388 X0 X1 X2
               grind)
            | exact resolve b6e9476 b6e956388
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e9476 b6e956388
          have b6e959085 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (τ (σ X0)) ∨ (M.op X0 X3) = (k X3 X0) := by
            intro X0 X1 X3
            first
            | (have i₁ := b6e3019 X0 x X1
               have i₂ := b6e956527 X0 X3 x
               grind)
            | exact superpose b6e956527 b6e3019
            | (have j1 := b6e956527 X0 X3 x
               grind)
            | exact resolve b6e3019 b6e956527
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e3019
          have b6e959120 : ∀ X0 X1 X3 : G, (τ (σ X0)) = (M.op (M.op (τ (σ X0)) X1) X1) ∨ (M.op X0 X3) = (k X3 X0) := by
            intro X0 X1 X3
            first
            | (have i₁ := b6e3437 (σ X0) x X1
               have i₂ := b6e956527 X0 X3 x
               grind)
            | exact superpose b6e956527 b6e3437
            | (have j1 := b6e956527 X0 X3 x
               grind)
            | exact resolve b6e3437 b6e956527
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e3437 b6e956527
          have b6e959142 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X1) = X0 ∨ (M.op X0 X3) = (k X3 X0) := by
            intro X0 X1 X3
            first
            | (have i₁ := b6e959120 X0 X1 X3
               have i₂ := b6e14 X0
               grind)
            | exact superpose b6e14 b6e959120
            | (have j0 := b6e959120 X0 X1 X3
               grind)
            | exact resolve b6e959120 b6e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e959120
          have b6e959163 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X3) = (k X3 X0) := by
            intro X0 X1 X3
            first
            | (have i₁ := b6e959085 X0 X1 X3
               have i₂ := b6e14 X0
               grind)
            | exact superpose b6e14 b6e959085
            | (have j0 := b6e959085 X0 X1 X3
               grind)
            | exact resolve b6e959085 b6e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e959085
          have b6e959561 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (τ (σ X0)) ∨ (M.op (σ X0) X3) = (k X3 (σ X0)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b6e8300 X0 x X1
               have i₂ := b6e959163 (σ X0) x X3
               grind)
            | exact superpose b6e959163 b6e8300
            | (have j1 := b6e959163 (σ X0) X1 X3
               grind)
            | exact resolve b6e8300 b6e959163
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e8300 b6e959163
          have b6e959643 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = X0 ∨ (M.op (σ X0) X3) = (k X3 (σ X0)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b6e959561 X0 X1 X3
               have i₂ := b6e14 X0
               grind)
            | exact superpose b6e14 b6e959561
            | (have j0 := b6e959561 X0 X1 X3
               grind)
            | exact resolve b6e959561 b6e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e959561
          have b6e959880 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b6e16823 X1
               have i₂ := b6e959142 X1 X1 x
               grind)
            | exact superpose b6e959142 b6e16823
            | (have j1 := b6e959142 X0 X1 X1
               grind)
            | exact resolve b6e16823 b6e959142
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e16823 b6e959142
          have b6e960178 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b6e959880 X0 X1
               have i₂ := b6e67 X0
               grind)
            | exact superpose b6e67 b6e959880
            | (have j0 := b6e959880 X0 X1
               grind)
            | exact resolve b6e959880 b6e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e67 b6e959880
          have b6e960564 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b6e14 (M.op X0 X0)
               have i₂ := b6e960178 X0 X1
               grind)
            | exact superpose b6e960178 b6e14
            | (have j1 := b6e960178 X0 X1
               grind)
            | exact resolve b6e14 b6e960178
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e960178
          have b6e960575 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b6e960564 X0 X1
               have i₂ := b6e14 X0
               grind)
            | exact superpose b6e14 b6e960564
            | (have j0 := b6e960564 X0 X1
               grind)
            | exact resolve b6e960564 b6e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e960564
          have b6e960754 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b6e26 X1 X0
               have i₂ := b6e960575 X0 (τ X1)
               grind)
            | exact superpose b6e960575 b6e26
            | (have j1 := b6e960575 X0 X1
               grind)
            | exact resolve b6e26 b6e960575
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e26 b6e960575
          have b6e961186 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b6e960754 X1 (σ X0)
               have i₂ := b6e14 X0
               grind)
            | exact superpose b6e14 b6e960754
            | (have j0 := b6e960754 X1 X1
               grind)
            | exact resolve b6e960754 b6e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e960754
          have b6e961210 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b6e961186 X0 X1
               have i₂ := b6e19 X0 X1
               grind)
            | exact superpose b6e19 b6e961186
            | (have j0 := b6e961186 X0 X1
               grind)
            | exact resolve b6e961186 b6e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e961186
          have b6e972071 : ∀ X1 : G, x = (M.op (M.op x x) y) ∨ (M.op (σ x) X1) = (k X1 (σ x)) := by
            intro X1
            first
            | (have i₁ := b6e13066 X1
               have i₂ := b6e959643 x X1 x
               grind)
            | exact superpose b6e959643 b6e13066
            | (have j1 := b6e959643 x X1 X1
               grind)
            | exact resolve b6e13066 b6e959643
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e13066 b6e959643
          have b6e985309 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) ∨ x = (M.op x x) := by
            intro X0
            first
            | (have i₁ := b6e488
               have i₂ := b6e972071 x
               grind)
            | exact superpose b6e972071 b6e488
            | (have j1 := b6e972071 X0
               grind)
            | exact resolve b6e488 b6e972071
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e488 b6e972071
          have b6e985468 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) ∨ x = (M.op x x) := by
            intro X0
            first
            | (have i₁ := b6e19 X0 x
               have i₂ := b6e985309 (σ X0)
               grind)
            | exact superpose b6e985309 b6e19
            | exact resolve b6e19 b6e985309
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e985309
          have b6e986184 : (σ (M.op x x)) ≠ (σ (k y x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b6e25
               have i₂ := b6e985468 y
               grind)
            | exact superpose b6e985468 b6e25
            | exact resolve b6e25 b6e985468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e985468
          have b6e986521 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b6e986184
               have i₂ := b6e961210 y x
               grind)
            | exact superpose b6e961210 b6e986184
            | (have j1 := b6e961210 x x
               grind)
            | exact resolve b6e986184 b6e961210
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e961210 b6e986184
          have b6e986523 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by grind
          clear b6e986521
          have b6e986529 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b6e986523
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e986523
            | exact resolve b6e986523 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e986523
          have b6e986530 : x = (M.op x x) := by grind
          clear b6e986529
          have b6e986997 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) X0) ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b6e151 x X0
               have i₂ := b6e986530
               grind)
            | exact superpose b6e986530 b6e151
            | (have j0 := b6e151 x X0
               grind)
            | exact resolve b6e151 b6e986530
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e151
          have b6e987021 : ∀ X0 : G, (σ X0) ≠ (σ x) ∨ (σ (k x X0)) = (M.op (σ X0) (σ x)) := by
            intro X0
            first
            | (have i₁ := b6e2442 X0 x
               have i₂ := b6e986530
               grind)
            | exact superpose b6e986530 b6e2442
            | (have j0 := b6e2442 X0 x
               grind)
            | exact resolve b6e2442 b6e986530
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e2442
          have b6e987339 : ∀ X0 : G, (σ (M.op x x)) = (M.op (M.op (σ (M.op x x)) X0) X0) := by
            intro X0
            first
            | (have i₁ := b6e3054 x x x
               have i₂ := b6e986530
               grind)
            | exact superpose b6e986530 b6e3054
            | exact resolve b6e3054 b6e986530
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e3054
          have b6e987916 : ∀ X0 : G, (M.op x x) = X0 ∨ (k x X0) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b6e956795 X0 x x
               have i₂ := b6e986530
               grind)
            | exact superpose b6e986530 b6e956795
            | (have j0 := b6e956795 X0 x x
               grind)
            | exact resolve b6e956795 b6e986530
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e956795
          have b6e987949 : ∀ X0 : G, (k x X0) = (M.op X0 x) := by
            intro X0
            first
            | (have j0 := b6e987916 X0
               have j1 := b6e273973 x X0
               grind)
            | (have r₁ := b6e987916 x
               have r₂ := b6e273973 x x
               grind)
            | (have r₁ := b6e987916 (M.op X0 X0)
               have r₂ := b6e273973 X0 (M.op x x)
               grind)
            | (have r₁ := b6e987916 x
               have r₂ := b6e273973 x (k x x)
               grind)
            | exact resolve b6e987916 b6e273973
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e273973 b6e987916
          have b6e988375 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) X0) X0) := by
            intro X0
            first
            | (have i₁ := b6e987339 X0
               have i₂ := b6e986530
               grind)
            | exact superpose b6e986530 b6e987339
            | exact resolve b6e987339 b6e986530
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e987339
          have b6e1011578 : ∀ X0 : G, (σ X0) = (σ x) ∨ (σ (k x X0)) = (M.op (σ X0) (σ x)) := by
            intro X0
            first
            | (have i₁ := b6e570442 X0 x x
               have i₂ := b6e988375 x
               grind)
            | exact superpose b6e988375 b6e570442
            | (have j0 := b6e570442 X0 x x
               grind)
            | exact resolve b6e570442 b6e988375
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e570442
          have b6e1011886 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b6e956773 X0 (σ x) x
               have i₂ := b6e988375 x
               grind)
            | exact superpose b6e988375 b6e956773
            | (have j0 := b6e956773 X0 (σ x) x
               grind)
            | exact resolve b6e956773 b6e988375
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e956773 b6e988375
          have b6e1012338 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have j0 := b6e1011886 X0
               have j1 := b6e986997 X0
               grind)
            | (have r₁ := b6e1011886 X0
               have r₂ := b6e986997 X0
               grind)
            | exact resolve b6e1011886 b6e986997
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e986997 b6e1011886
          have b6e1012558 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) := by
            intro X0
            first
            | (have j0 := b6e1011578 X0
               have j1 := b6e987021 X0
               grind)
            | (have r₁ := b6e1011578 X0
               have r₂ := b6e987021 X0
               grind)
            | (have r₁ := b6e1011578 x
               have r₂ := b6e987021 x
               grind)
            | exact resolve b6e1011578 b6e987021
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e987021 b6e1011578
          have b6e1013137 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b6e1012558 X0
               have i₂ := b6e987949 X0
               grind)
            | exact superpose b6e987949 b6e1012558
            | exact resolve b6e1012558 b6e987949
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1012558
          have b6e1019438 : ∀ X0 : G, (k x (τ X0)) = (τ (M.op X0 (σ x))) := by
            intro X0
            first
            | (have i₁ := b6e44 x X0
               have i₂ := b6e1012338 X0
               grind)
            | exact superpose b6e1012338 b6e44
            | exact resolve b6e44 b6e1012338
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e44 b6e1012338
          have b6e1019506 : ∀ X0 : G, (M.op (τ X0) x) = (τ (M.op X0 (σ x))) := by
            intro X0
            first
            | (have i₁ := b6e1019438 X0
               have i₂ := b6e987949 (τ X0)
               grind)
            | exact superpose b6e987949 b6e1019438
            | exact resolve b6e1019438 b6e987949
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e987949 b6e1019438
          have b6e1027181 : ∀ X0 : G, (τ (σ x)) = (M.op (τ (σ X0)) x) ∨ (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
            intro X0
            first
            | (have i₁ := b6e1019506 (σ X0)
               have i₂ := b6e258 x X0
               grind)
            | exact superpose b6e258 b6e1019506
            | (have j1 := b6e258 x X0
               grind)
            | exact resolve b6e1019506 b6e258
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e258 b6e1019506
          have b6e1027500 : ∀ X0 : G, (M.op X0 x) = (τ (σ x)) ∨ (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
            intro X0
            first
            | (have i₁ := b6e1027181 X0
               have i₂ := b6e14 X0
               grind)
            | exact superpose b6e14 b6e1027181
            | (have j0 := b6e1027181 X0
               grind)
            | exact resolve b6e1027181 b6e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1027181
          have b6e1027648 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) ∨ x = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b6e1027500 X0
               have i₂ := b6e14 x
               grind)
            | exact superpose b6e14 b6e1027500
            | (have j0 := b6e1027500 X0
               grind)
            | exact resolve b6e1027500 b6e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1027500
          have b6e1156645 : (σ (M.op x x)) ≠ (σ (k y x)) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b6e25
               have i₂ := b6e1027648 y
               grind)
            | exact superpose b6e1027648 b6e25
            | (have j1 := b6e1027648 y
               grind)
            | exact resolve b6e25 b6e1027648
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1027648
          have b6e1156660 : (σ x) ≠ (σ (k y x)) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b6e1156645
               have i₂ := b6e986530
               grind)
            | exact superpose b6e986530 b6e1156645
            | exact resolve b6e1156645 b6e986530
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1156645
          have b6e1156758 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b6e1156660
               have i₂ := b6e13623 y x
               grind)
            | exact superpose b6e13623 b6e1156660
            | (have j1 := b6e13623 y x
               grind)
            | exact resolve b6e1156660 b6e13623
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e13623 b6e1156660
          have b6e1156759 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y x) := by grind
          clear b6e1156758
          have b6e1156761 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b6e1156759
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e1156759
            | exact resolve b6e1156759 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1156759
          have b6e1156763 : (σ x) ≠ (σ x) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b6e1156761
               have i₂ := b6e986530
               grind)
            | exact superpose b6e986530 b6e1156761
            | exact resolve b6e1156761 b6e986530
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e986530 b6e1156761
          have b6e1156764 : x = (M.op y x) := by grind
          clear b6e1156763
          have b6e1157017 : ∀ X0 : G, (σ (M.op y x)) = (M.op (M.op (σ y) X0) X0) := by
            intro X0
            first
            | (have i₁ := b6e2495 y x X0
               have i₂ := b6e1156764
               grind)
            | exact superpose b6e1156764 b6e2495
            | exact resolve b6e2495 b6e1156764
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e2495
          have b6e1157026 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op y X0)) X1) X1) = (σ (M.op (M.op y x) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b6e2706 y x X0 X1
               have i₂ := b6e1156764
               grind)
            | exact superpose b6e1156764 b6e2706
            | exact resolve b6e2706 b6e1156764
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e2706
          have b6e1157848 : ∀ X0 X1 : G, (σ (M.op x X0)) = (M.op (M.op (σ (M.op y X0)) X1) X1) := by
            intro X0 X1
            first
            | (have i₁ := b6e1157026 X0 X1
               have i₂ := b6e1156764
               grind)
            | exact superpose b6e1156764 b6e1157026
            | exact resolve b6e1157026 b6e1156764
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1157026
          have b6e1157855 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) X0) := by
            intro X0
            first
            | (have i₁ := b6e1157017 X0
               have i₂ := b6e1156764
               grind)
            | exact superpose b6e1156764 b6e1157017
            | exact resolve b6e1157017 b6e1156764
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1157017
          have b6e1184129 : ∀ X0 : G, (M.op (M.op (σ (M.op y y)) X0) X0) = (M.op (M.op (σ y) (σ x)) (σ y)) := by
            intro X0
            first
            | (have i₁ := b6e21735 y X0 x
               have i₂ := b6e1157855 x
               grind)
            | exact superpose b6e1157855 b6e21735
            | exact resolve b6e21735 b6e1157855
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e21735 b6e1157855
          have b6e1185134 : ∀ X0 : G, (M.op (σ (M.op y x)) (σ y)) = (M.op (M.op (σ (M.op y y)) X0) X0) := by
            intro X0
            first
            | (have i₁ := b6e1184129 X0
               have i₂ := b6e1013137 y
               grind)
            | exact superpose b6e1013137 b6e1184129
            | exact resolve b6e1184129 b6e1013137
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1013137 b6e1184129
          have b6e1185757 : (σ (M.op x y)) = (M.op (σ (M.op y x)) (σ y)) := by
            first
            | (have i₁ := b6e1185134 x
               have i₂ := b6e1157848 y x
               grind)
            | exact superpose b6e1157848 b6e1185134
            | exact resolve b6e1185134 b6e1157848
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1157848 b6e1185134
          have b6e1186180 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b6e1185757
               have i₂ := b6e1156764
               grind)
            | exact superpose b6e1156764 b6e1185757
            | exact resolve b6e1185757 b6e1156764
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1156764 b6e1185757
          have b6e1186410 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b6e1186180
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e1186180
            | exact resolve b6e1186180 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1186180
          have b6e1186521 : False := by grind
          exact b6e1186521
        · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
          · have b7e25 : (M.op x x) ≠ (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e27 : False := by grind
            exact b7e27
          · have b8e25 : (M.op x x) ≠ (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e27 : False := by grind
            exact b8e27
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x x) (M.op x x) with h2a | h2a
        · have b9e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X2) := by
            intro X0 X1 X2
            grind
          have b9e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b9e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b9e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b9e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b9e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b9e22 : y = (M.op x y) := by grind
          have b9e23 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e25 : y ≠ (M.op x x) := by
            first
            | (have i₁ := b9e21
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e21
            | exact resolve b9e21 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e26 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b9e20
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e20
            | exact resolve b9e20 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e27 : (σ y) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b9e26
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e26
            | exact resolve b9e26 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e26
          have b9e34 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) X3) = (M.op X0 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b9e13 X0 (M.op X0 x) X3
               have i₂ := b9e13 X0 x X1
               grind)
            | exact superpose b9e13 b9e13
            | exact resolve b9e13 b9e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e36 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X3) X3) := by
            intro X0 X1 X3
            first
            | (have i₁ := b9e13 X0 x X3
               have i₂ := b9e13 X0 x X1
               grind)
            | exact superpose b9e13 b9e13
            | exact resolve b9e13 b9e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e37 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op y y) := by
            intro X0
            first
            | (have i₁ := b9e13 x X0 y
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e13
            | exact resolve b9e13 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e41 : (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b9e37 y
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e37
            | exact resolve b9e37 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e37
          have b9e50 : y = (M.op y y) := by
            first
            | (have i₁ := b9e41
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e41
            | exact resolve b9e41 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e41
          have b9e51 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
            intro X0
            first
            | (have i₁ := b9e13 (σ x) X0 (σ y)
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e13
            | exact resolve b9e13 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e56 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b9e16 (σ x) (σ y)
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e16
            | (have j0 := b9e16 (σ x) (σ x)
               grind)
            | (have r₁ := b9e16 (σ x) (σ y)
               have r₂ := b9e23
               grind)
            | exact resolve b9e16 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e61 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b9e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e63 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
          clear b9e56
          have b9e66 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b9e63
               have i₂ := b9e19 x y
               grind)
            | exact superpose b9e19 b9e63
            | exact resolve b9e63 b9e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e63
          have b9e68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b9e19 X0 X0
               have i₂ := b9e61 (σ X0)
               grind)
            | exact superpose b9e61 b9e19
            | exact resolve b9e19 b9e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e71 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b9e68 X0
               have i₂ := b9e61 X0
               grind)
            | exact superpose b9e61 b9e68
            | exact resolve b9e68 b9e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e61 b9e68
          have b9e76 : y ≠ y ∨ y = (M.op x x) ∨ (M.op x x) = (k x y) := by
            first
            | (have i₁ := b9e17 x y
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e17
            | (have j0 := b9e17 x y
               grind)
            | (have r₁ := b9e17 x y
               have r₂ := b9e22
               grind)
            | exact resolve b9e17 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e78 : y = (M.op x x) ∨ (M.op x x) = (k x y) := by grind
          clear b9e76
          have b9e80 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b9e78
               have r₂ := b9e25
               grind)
            | exact resolve b9e78 b9e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e25 b9e78
          have b9e139 : ∀ X0 : G, (M.op (M.op (σ y) X0) X0) = (M.op (σ y) (σ (k x y))) := by
            intro X0
            first
            | (have i₁ := b9e13 (σ y) (σ x) X0
               have i₂ := b9e66
               grind)
            | exact superpose b9e66 b9e13
            | exact resolve b9e13 b9e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e140 : ∀ X0 : G, (M.op (M.op (σ y) X0) X0) = (M.op (σ y) (σ (M.op x x))) := by
            intro X0
            first
            | (have i₁ := b9e139 X0
               have i₂ := b9e80
               grind)
            | exact superpose b9e80 b9e139
            | exact resolve b9e139 b9e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e139
          have b9e186 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (σ y)) = (M.op (M.op (σ x) X0) X0) := by
            intro X0
            first
            | (have i₁ := b9e36 (σ x) X0 (σ y)
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e36
            | exact resolve b9e36 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e187 : ∀ X0 : G, (M.op (σ (k x y)) (σ x)) = (M.op (M.op (σ y) X0) X0) := by
            intro X0
            first
            | (have i₁ := b9e36 (σ y) X0 (σ x)
               have i₂ := b9e66
               grind)
            | exact superpose b9e66 b9e36
            | exact resolve b9e36 b9e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e66
          have b9e210 : ∀ X0 : G, (M.op (M.op (σ y) X0) X0) = (M.op (σ (M.op x x)) (σ x)) := by
            intro X0
            first
            | (have i₁ := b9e187 X0
               have i₂ := b9e80
               grind)
            | exact superpose b9e80 b9e187
            | exact resolve b9e187 b9e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e80 b9e187
          have b9e211 : ∀ X0 : G, (M.op (M.op (σ x) X0) X0) = (M.op (σ (M.op x x)) (σ y)) := by
            intro X0
            first
            | (have i₁ := b9e186 X0
               have i₂ := b9e71 x
               grind)
            | exact superpose b9e71 b9e186
            | exact resolve b9e186 b9e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e186
          have b9e1421 : (M.op (σ (M.op x x)) (σ y)) = (M.op (σ x) (σ (M.op x x))) := by
            first
            | (have i₁ := b9e51 (σ x)
               have i₂ := b9e71 x
               grind)
            | exact superpose b9e71 b9e51
            | exact resolve b9e51 b9e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e51
          have b9e1426 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (M.op (M.op (σ X0) X1) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b9e34 (σ X0) X1 (σ X0)
               have i₂ := b9e71 X0
               grind)
            | exact superpose b9e71 b9e34
            | exact resolve b9e34 b9e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e3517 : (M.op (σ y) (σ (M.op x x))) = (M.op (σ (M.op y y)) (σ y)) := by
            first
            | (have i₁ := b9e140 (σ y)
               have i₂ := b9e71 y
               grind)
            | exact superpose b9e71 b9e140
            | exact resolve b9e140 b9e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e3586 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ y) X0) X0) (σ (M.op x x))) = (M.op (σ y) (M.op (M.op (σ y) X1) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b9e34 (σ y) X1 (σ (M.op x x))
               have i₂ := b9e140 X0
               grind)
            | exact superpose b9e140 b9e34
            | exact resolve b9e34 b9e140
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e34
          have b9e3612 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) X0) (σ (M.op x x))) = (M.op (σ (M.op y y)) (σ y)) := by
            intro X0
            first
            | (have i₁ := b9e3586 X0 x
               have i₂ := b9e1426 y x
               grind)
            | exact superpose b9e1426 b9e3586
            | exact resolve b9e3586 b9e1426
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e1426 b9e3586
          have b9e3634 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ (M.op x x))) := by
            first
            | (have i₁ := b9e3517
               have i₂ := b9e50
               grind)
            | exact superpose b9e50 b9e3517
            | exact resolve b9e3517 b9e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e3517
          have b9e3640 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (M.op (σ y) X0) X0) (σ (M.op x x))) := by
            intro X0
            first
            | (have i₁ := b9e3612 X0
               have i₂ := b9e50
               grind)
            | exact superpose b9e50 b9e3612
            | exact resolve b9e3612 b9e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e3612
          have b9e3660 : (M.op (σ y) (σ (M.op x x))) = (σ (M.op y y)) := by
            first
            | (have i₁ := b9e3634
               have i₂ := b9e71 y
               grind)
            | exact superpose b9e71 b9e3634
            | exact resolve b9e3634 b9e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e3634
          have b9e3664 : ∀ X0 : G, (σ (M.op y y)) = (M.op (M.op (M.op (σ y) X0) X0) (σ (M.op x x))) := by
            intro X0
            first
            | (have i₁ := b9e3640 X0
               have i₂ := b9e71 y
               grind)
            | exact superpose b9e71 b9e3640
            | exact resolve b9e3640 b9e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e3640
          have b9e3682 : (σ y) = (M.op (σ y) (σ (M.op x x))) := by
            first
            | (have i₁ := b9e3660
               have i₂ := b9e50
               grind)
            | exact superpose b9e50 b9e3660
            | exact resolve b9e3660 b9e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e3660
          have b9e3684 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ y) X0) X0) (σ (M.op x x))) := by
            intro X0
            first
            | (have i₁ := b9e3664 X0
               have i₂ := b9e50
               grind)
            | exact superpose b9e50 b9e3664
            | exact resolve b9e3664 b9e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e50 b9e3664
          have b9e3797 : ∀ X0 : G, (M.op (σ (M.op x x)) (σ x)) = (M.op (M.op (M.op (σ y) X0) X0) (σ (M.op x x))) := by
            intro X0
            first
            | (have i₁ := b9e210 (σ (M.op x x))
               have i₂ := b9e140 X0
               grind)
            | exact superpose b9e140 b9e210
            | exact resolve b9e210 b9e140
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e140 b9e210
          have b9e3951 : (σ y) = (M.op (σ (M.op x x)) (σ x)) := by
            first
            | (have i₁ := b9e3797 x
               have i₂ := b9e3684 x
               grind)
            | exact superpose b9e3684 b9e3797
            | exact resolve b9e3797 b9e3684
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e3684 b9e3797
          have b9e4259 : (M.op (σ (M.op x x)) (σ x)) = (M.op (σ (M.op x x)) (σ y)) := by
            first
            | (have i₁ := b9e211 (σ x)
               have i₂ := b9e71 x
               grind)
            | exact superpose b9e71 b9e211
            | exact resolve b9e211 b9e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e71 b9e211
          have b9e4402 : (M.op (σ (M.op x x)) (σ x)) = (M.op (σ x) (σ (M.op x x))) := by
            first
            | (have i₁ := b9e4259
               have i₂ := b9e1421
               grind)
            | exact superpose b9e1421 b9e4259
            | exact resolve b9e4259 b9e1421
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e1421 b9e4259
          have b9e4432 : (σ y) = (M.op (σ x) (σ (M.op x x))) := by
            first
            | (have i₁ := b9e4402
               have i₂ := b9e3951
               grind)
            | exact superpose b9e3951 b9e4402
            | exact resolve b9e4402 b9e3951
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e3951 b9e4402
          have b9e4563 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) X0) X0) := by
            intro X0
            first
            | (have i₁ := b9e13 (σ x) (σ (M.op x x)) X0
               have i₂ := b9e4432
               grind)
            | exact superpose b9e4432 b9e13
            | exact resolve b9e13 b9e4432
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e4572 : ∀ X0 : G, (M.op (M.op (σ x) X0) X0) = (M.op (σ y) (σ (M.op x x))) := by
            intro X0
            first
            | (have i₁ := b9e36 (σ x) X0 (σ (M.op x x))
               have i₂ := b9e4432
               grind)
            | exact superpose b9e4432 b9e36
            | exact resolve b9e36 b9e4432
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e36 b9e4432
          have b9e4604 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) X0) := by
            intro X0
            first
            | (have i₁ := b9e4572 X0
               have i₂ := b9e3682
               grind)
            | exact superpose b9e3682 b9e4572
            | exact resolve b9e4572 b9e3682
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e3682 b9e4572
          have b9e4611 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) X0) X0) := by
            intro X0
            first
            | (have i₁ := b9e4563 X0
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e4563
            | exact resolve b9e4563 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e4563
          have b9e4627 : (σ y) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b9e4611 x
               have i₂ := b9e4604 x
               grind)
            | exact superpose b9e4604 b9e4611
            | exact resolve b9e4611 b9e4604
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e4604 b9e4611
          have b9e4640 : False := by grind
          exact b9e4640
        · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
          · have b10e25 : (M.op x x) ≠ (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e27 : False := by grind
            exact b10e27
          · have b11e25 : (M.op x x) ≠ (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e27 : False := by grind
            exact b11e27
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op x x) (M.op x x) with h2a | h2a
          · have b12e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b12e23 : y = (M.op x y) := by grind
            have b12e25 : (σ y) = (M.op (σ x) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e29 : (σ (M.op x y)) ≠ (σ y) := by
              first
              | (have i₁ := b12e21
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e21
              | exact resolve b12e21 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e30 : (σ y) ≠ (σ y) := by
              first
              | (have i₁ := b12e29
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e29
              | exact resolve b12e29 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e29
            have b12e31 : False := by grind
            exact b12e31
          · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
            · have b13e27 : (M.op x x) ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e29 : False := by grind
              exact b13e29
            · have b14e27 : (M.op x x) ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e29 : False := by grind
              exact b14e29
        · rcases eq_or_ne (M.op x x) (M.op x x) with h2a | h2a
          · have b15e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X2) := by
              intro X0 X1 X2
              grind
            have b15e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b15e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
              intro X0 X1
              grind
            have b15e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              grind
            have b15e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b15e23 : y = (M.op x y) := by grind
            have b15e25 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b15e20 (τ X0) X1
                 have i₂ := b15e16 X0
                 grind)
              | exact superpose b15e16 b15e20
              | exact resolve b15e20 b15e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e35 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) X3) = (M.op X0 (M.op (M.op X0 X1) X1)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b15e14 X0 (M.op X0 x) X3
                 have i₂ := b15e14 X0 x X1
                 grind)
              | exact superpose b15e14 b15e14
              | exact resolve b15e14 b15e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e37 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X3) X3) := by
              intro X0 X1 X3
              first
              | (have i₁ := b15e14 X0 x X3
                 have i₂ := b15e14 X0 x X1
                 grind)
              | exact superpose b15e14 b15e14
              | exact resolve b15e14 b15e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e41 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b15e14 X0 X1 x
                 have i₂ := b15e14 X0 X2 x
                 grind)
              | exact superpose b15e14 b15e14
              | exact resolve b15e14 b15e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e59 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
              intro X0
              first
              | (have j0 := b15e17 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e64 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have i₁ := b15e20 X0 X0
                 have i₂ := b15e59 (σ X0)
                 grind)
              | exact superpose b15e59 b15e20
              | exact resolve b15e20 b15e59
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e65 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
              intro X0
              first
              | (have i₁ := b15e29 X0 (τ X0)
                 have i₂ := b15e59 (τ X0)
                 grind)
              | exact superpose b15e59 b15e29
              | exact resolve b15e29 b15e59
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e66 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
              intro X0
              first
              | (have i₁ := b15e65 X0
                 have i₂ := b15e16 X0
                 grind)
              | exact superpose b15e16 b15e65
              | exact resolve b15e65 b15e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e65
            have b15e67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b15e64 X0
                 have i₂ := b15e59 X0
                 grind)
              | exact superpose b15e59 b15e64
              | exact resolve b15e64 b15e59
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e64
            have b15e69 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
              intro X0
              first
              | (have i₁ := b15e66 X0
                 have i₂ := b15e59 X0
                 grind)
              | exact superpose b15e59 b15e66
              | exact resolve b15e66 b15e59
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e59 b15e66
            have b15e82 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1
              first
              | (have i₁ := b15e20 X1 X0
                 have i₂ := b15e19 (σ X1) (σ X0)
                 grind)
              | exact superpose b15e19 b15e20
              | (have j1 := b15e19 (σ X1) (σ X0)
                 grind)
              | exact resolve b15e20 b15e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e97 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1
              first
              | (have i₁ := b15e82 X0 X1
                 have i₂ := b15e67 X1
                 grind)
              | exact superpose b15e67 b15e82
              | (have j0 := b15e82 X0 X1
                 grind)
              | exact resolve b15e82 b15e67
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e82
            have b15e220 : ∀ X0 : G, (M.op x y) = (M.op x (M.op x X0)) := by
              intro X0
              first
              | (have i₁ := b15e41 x X0 y
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e41
              | exact resolve b15e41 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e260 : ∀ X0 : G, y = (M.op x (M.op x X0)) := by
              intro X0
              first
              | (have i₁ := b15e220 X0
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e220
              | exact resolve b15e220 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e220
            have b15e283 : ∀ X1 : G, y = (M.op (M.op x X1) X1) := by
              intro X1
              first
              | (have i₁ := b15e14 x x X1
                 have i₂ := b15e260 x
                 grind)
              | exact superpose b15e260 b15e14
              | exact resolve b15e14 b15e260
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e260
            have b15e366 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X2) = (M.op X0 (M.op (M.op X0 (M.op X0 X1)) (M.op X0 X3))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b15e35 X0 (M.op X0 X3) X2
                 have i₂ := b15e41 X0 X3 X1
                 grind)
              | (have i₁ := b15e35 X0 (M.op X0 X3) X2
                 have i₂ := b15e41 X0 X1 X3
                 grind)
              | exact superpose b15e41 b15e35
              | exact resolve b15e35 b15e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e35 b15e41
            have b15e1492 : ∀ X0 X1 : G, (M.op (M.op (σ X0) X1) X1) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
              intro X0 X1
              first
              | (have i₁ := b15e37 (σ X0) X1 (σ X0)
                 have i₂ := b15e67 X0
                 grind)
              | exact superpose b15e67 b15e37
              | exact resolve b15e37 b15e67
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e37
            have b15e1506 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
              intro X0 X1
              first
              | (have i₁ := b15e17 (σ X0) X1
                 have i₂ := b15e67 X0
                 grind)
              | exact superpose b15e67 b15e17
              | (have j0 := b15e17 (σ X0) X1
                 grind)
              | exact resolve b15e17 b15e67
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e2044 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
              intro X0 X1
              first
              | (have i₁ := b15e17 (σ X1) (σ X0)
                 have i₂ := b15e97 X0 X1
                 grind)
              | exact superpose b15e97 b15e17
              | (have j0 := b15e17 (σ X1) (σ X0)
                 have j1 := b15e97 X0 X1
                 grind)
              | exact resolve b15e17 b15e97
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e97
            have b15e2079 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
              intro X0 X1
              first
              | (have j0 := b15e2044 X0 X1
                 have j1 := b15e1506 X1 (σ X0)
                 grind)
              | (have r₁ := b15e2044 X0 X0
                 have r₂ := b15e1506 X0 (σ X0)
                 grind)
              | exact resolve b15e2044 b15e1506
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e1506 b15e2044
            have b15e2111 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
              intro X0 X1
              first
              | (have i₁ := b15e2079 X0 X1
                 have i₂ := b15e67 X1
                 grind)
              | exact superpose b15e67 b15e2079
              | (have j0 := b15e2079 X0 X1
                 grind)
              | (have r₁ := b15e2079 (M.op X0 X0) X0
                 have r₂ := b15e67 X0
                 grind)
              | exact resolve b15e2079 b15e67
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e67 b15e2079
            have b15e2128 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
              intro X0 X1
              first
              | (have i₁ := b15e2111 X0 X1
                 have i₂ := b15e20 X1 X0
                 grind)
              | exact superpose b15e20 b15e2111
              | (have j0 := b15e2111 X0 X1
                 grind)
              | exact resolve b15e2111 b15e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e2111
            have b15e2129 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
              intro X0 X1
              first
              | (have j0 := b15e2128 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e2128
            have b15e30333 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k X0 (M.op X0 X0))) := by
              intro X0
              first
              | (have j0 := b15e2129 (M.op X0 X0) X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e2129
            have b15e30380 : ∀ X0 : G, (M.op (σ (M.op (τ X0) (τ X0))) X0) = (σ (k (τ X0) (M.op (τ X0) (τ X0)))) := by
              intro X0
              first
              | (have i₁ := b15e30333 (τ X0)
                 have i₂ := b15e16 X0
                 grind)
              | exact superpose b15e16 b15e30333
              | exact resolve b15e30333 b15e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e30389 : ∀ X0 X1 : G, (M.op (M.op (σ X0) X1) X1) = (σ (k X0 (M.op X0 X0))) := by
              intro X0 X1
              first
              | (have i₁ := b15e1492 X0 X1
                 have i₂ := b15e30333 X0
                 grind)
              | exact superpose b15e30333 b15e1492
              | exact resolve b15e1492 b15e30333
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e1492 b15e30333
            have b15e30473 : ∀ X0 : G, (M.op (σ (M.op (τ X0) (τ X0))) X0) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
              intro X0
              first
              | (have i₁ := b15e30380 X0
                 have i₂ := b15e29 X0 (M.op (τ X0) (τ X0))
                 grind)
              | exact superpose b15e29 b15e30380
              | exact resolve b15e30380 b15e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e29 b15e30380
            have b15e30493 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b15e30473 X0
                 have i₂ := b15e69 X0
                 grind)
              | exact superpose b15e69 b15e30473
              | exact resolve b15e30473 b15e69
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e69 b15e30473
            have b15e32095 : ∀ X0 X1 : G, (M.op (M.op (σ X0) X1) X1) = (σ (M.op (M.op X0 X0) X0)) := by
              intro X0 X1
              first
              | (have i₁ := b15e30389 X0 X1
                 have i₂ := b15e30493 X0
                 grind)
              | exact superpose b15e30493 b15e30389
              | exact resolve b15e30389 b15e30493
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e30389 b15e30493
            have b15e40144 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) X0) := by
              intro X0
              first
              | (have i₁ := b15e32095 x X0
                 have i₂ := b15e283 x
                 grind)
              | exact superpose b15e283 b15e32095
              | exact resolve b15e32095 b15e283
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e283 b15e32095
            have b15e42179 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) X0) X0) := by
              intro X0
              first
              | (have i₁ := b15e366 (σ x) x X0 x
                 have i₂ := b15e40144 (M.op (σ x) x)
                 grind)
              | exact superpose b15e40144 b15e366
              | exact resolve b15e366 b15e40144
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e366
            have b15e42351 : (σ y) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b15e42179 x
                 have i₂ := b15e40144 x
                 grind)
              | exact superpose b15e40144 b15e42179
              | exact resolve b15e42179 b15e40144
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e40144 b15e42179
            have b15e42535 : False := by grind
            exact b15e42535
          · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
            · have b16e27 : (M.op x x) ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e29 : False := by grind
              exact b16e29
            · have b17e27 : (M.op x x) ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e29 : False := by grind
              exact b17e29
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x x) (M.op x x) with h2a | h2a
        · have b18e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X2) := by
            intro X0 X1 X2
            grind
          have b18e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b18e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b18e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b18e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b18e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b18e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b18e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b18e22 : y ≠ (M.op x y) := by grind
          have b18e23 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e25 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b18e20
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e20
            | exact resolve b18e20 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b18e19 X1 (τ X0)
               have i₂ := b18e15 X0
               grind)
            | exact superpose b18e15 b18e19
            | exact resolve b18e19 b18e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e32 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) X3) = (M.op X0 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b18e13 X0 (M.op X0 x) X3
               have i₂ := b18e13 X0 x X1
               grind)
            | exact superpose b18e13 b18e13
            | exact resolve b18e13 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e34 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X3) X3) := by
            intro X0 X1 X3
            first
            | (have i₁ := b18e13 X0 x X3
               have i₂ := b18e13 X0 x X1
               grind)
            | exact superpose b18e13 b18e13
            | exact resolve b18e13 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e35 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X2)) = (M.op (M.op (M.op X0 X1) X1) (M.op X0 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b18e13 X0 X2 (M.op X0 X3)
               have i₂ := b18e13 X0 X3 X1
               grind)
            | exact superpose b18e13 b18e13
            | exact resolve b18e13 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op (M.op X0 X2) X3)) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b18e13 (M.op X0 X2) X3 X2
               have i₂ := b18e13 X0 X1 X2
               grind)
            | exact superpose b18e13 b18e13
            | exact resolve b18e13 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e37 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b18e13 X0 X1 x
               have i₂ := b18e13 X0 X2 x
               grind)
            | exact superpose b18e13 b18e13
            | exact resolve b18e13 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e43 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b18e14 (k X0 (τ X1))
               have i₂ := b18e27 X1 X0
               grind)
            | exact superpose b18e27 b18e14
            | exact resolve b18e14 b18e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e46 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
            intro X0
            first
            | (have i₁ := b18e13 (σ x) X0 (σ y)
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e13
            | exact resolve b18e13 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e57 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b18e16 (σ x) (σ y)
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e16
            | (have j0 := b18e16 (σ x) (σ x)
               grind)
            | (have r₁ := b18e16 (σ x) (σ y)
               have r₂ := b18e23
               grind)
            | exact resolve b18e16 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e58 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b18e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e59 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
          clear b18e57
          have b18e60 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b18e59
               have i₂ := b18e19 x y
               grind)
            | exact superpose b18e19 b18e59
            | exact resolve b18e59 b18e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e59
          have b18e62 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b18e19 X0 X0
               have i₂ := b18e58 (σ X0)
               grind)
            | exact superpose b18e58 b18e19
            | exact resolve b18e19 b18e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e64 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
            intro X0
            first
            | (have i₁ := b18e27 X0 (τ X0)
               have i₂ := b18e58 (τ X0)
               grind)
            | exact superpose b18e58 b18e27
            | exact resolve b18e27 b18e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e27
          have b18e67 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b18e64 X0
               have i₂ := b18e15 X0
               grind)
            | exact superpose b18e15 b18e64
            | exact resolve b18e64 b18e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e64
          have b18e69 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b18e62 X0
               have i₂ := b18e58 X0
               grind)
            | exact superpose b18e58 b18e62
            | exact resolve b18e62 b18e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e62
          have b18e72 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b18e67 X0
               have i₂ := b18e58 X0
               grind)
            | exact superpose b18e58 b18e67
            | exact resolve b18e67 b18e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e67
          have b18e79 : ∀ X0 : G, (M.op (M.op (σ y) X0) X0) = (M.op (σ y) (σ (k x y))) := by
            intro X0
            first
            | (have i₁ := b18e13 (σ y) (σ x) X0
               have i₂ := b18e60
               grind)
            | exact superpose b18e60 b18e13
            | exact resolve b18e13 b18e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e85 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b18e19 X1 X0
               have i₂ := b18e18 (σ X1) (σ X0)
               grind)
            | exact superpose b18e18 b18e19
            | (have j1 := b18e18 (σ X1) (σ X0)
               grind)
            | exact resolve b18e19 b18e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e89 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b18e16 X0 X1
               have i₂ := b18e18 X0 X1
               grind)
            | (have i₁ := b18e16 X0 X0
               have i₂ := b18e18 X0 X1
               grind)
            | exact superpose b18e18 b18e16
            | (have j0 := b18e16 X0 X0
               have j1 := b18e18 X0 X1
               grind)
            | (have r₁ := b18e16 X0 X1
               have r₂ := b18e18 X0 X1
               grind)
            | (have r₁ := b18e16 X1 X1
               have r₂ := b18e18 X1 X1
               grind)
            | (have r₁ := b18e16 X0 (M.op X0 X0)
               have r₂ := b18e18 X0 (M.op X0 X0)
               grind)
            | exact resolve b18e16 b18e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e97 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b18e18 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e99 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b18e89 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e89
          have b18e100 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b18e99 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e99
          have b18e102 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b18e85 X0 X1
               have i₂ := b18e69 X1
               grind)
            | exact superpose b18e69 b18e85
            | (have j0 := b18e85 X0 X1
               grind)
            | exact resolve b18e85 b18e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e85
          have b18e133 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X2) = (M.op (M.op (M.op X0 X1) X1) (M.op X0 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b18e34 X0 X2 (M.op X0 X3)
               have i₂ := b18e13 X0 X3 X1
               grind)
            | exact superpose b18e13 b18e34
            | exact resolve b18e34 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e137 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X2) X3) X3) = (M.op (M.op (M.op X0 X1) X1) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b18e34 (M.op X0 X2) X3 X2
               have i₂ := b18e34 X0 X2 X1
               grind)
            | (have i₁ := b18e34 (M.op X0 X2) X3 X2
               have i₂ := b18e34 X0 X1 X2
               grind)
            | exact superpose b18e34 b18e34
            | exact resolve b18e34 b18e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e139 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (σ y)) = (M.op (M.op (σ x) X0) X0) := by
            intro X0
            first
            | (have i₁ := b18e34 (σ x) X0 (σ y)
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e34
            | exact resolve b18e34 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e152 : ∀ X0 : G, (M.op (M.op (σ x) X0) X0) = (M.op (σ (M.op x x)) (σ y)) := by
            intro X0
            first
            | (have i₁ := b18e139 X0
               have i₂ := b18e69 x
               grind)
            | exact superpose b18e69 b18e139
            | exact resolve b18e139 b18e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e139
          have b18e158 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b18e25
               have i₂ := b18e69 x
               grind)
            | exact superpose b18e69 b18e25
            | exact resolve b18e25 b18e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e25
          have b18e159 : ∀ X0 X1 : G, (M.op (M.op (σ X0) X1) X1) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b18e13 (σ X0) (σ X0) X1
               have i₂ := b18e69 X0
               grind)
            | exact superpose b18e69 b18e13
            | exact resolve b18e13 b18e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e163 : ∀ X0 X1 : G, (M.op (M.op (σ X0) X1) X1) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b18e34 (σ X0) X1 (σ X0)
               have i₂ := b18e69 X0
               grind)
            | exact superpose b18e69 b18e34
            | exact resolve b18e34 b18e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e165 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b18e16 (σ X0) X1
               have i₂ := b18e69 X0
               grind)
            | exact superpose b18e69 b18e16
            | (have j0 := b18e16 (σ X0) X1
               grind)
            | exact resolve b18e16 b18e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e192 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ X0) (M.op (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b18e37 (σ X0) X1 (σ X0)
               have i₂ := b18e69 X0
               grind)
            | exact superpose b18e69 b18e37
            | exact resolve b18e37 b18e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e205 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X2)) = (M.op (M.op X0 (M.op X0 X1)) (M.op X0 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b18e13 X0 X2 (M.op X0 X3)
               have i₂ := b18e37 X0 X3 X1
               grind)
            | (have i₁ := b18e13 X0 X2 (M.op X0 X3)
               have i₂ := b18e37 X0 X1 X3
               grind)
            | exact superpose b18e37 b18e13
            | exact resolve b18e13 b18e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e206 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 X0) ∨ (k X0 (M.op X0 X2)) = (M.op (M.op X0 X2) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b18e16 X0 (M.op X0 X2)
               have i₂ := b18e37 X0 X2 X1
               grind)
            | (have i₁ := b18e16 X0 (M.op X0 X2)
               have i₂ := b18e37 X0 X1 X2
               grind)
            | exact superpose b18e37 b18e16
            | (have j0 := b18e16 X0 (M.op X0 X1)
               grind)
            | exact resolve b18e16 b18e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e211 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b18e19 X1 X0
               have i₂ := b18e100 (σ X1) (σ X0)
               grind)
            | exact superpose b18e100 b18e19
            | (have j1 := b18e100 (σ X1) (σ X0)
               grind)
            | exact resolve b18e19 b18e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e212 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b18e43 X1 X0
               have i₂ := b18e100 (σ X1) X0
               grind)
            | exact superpose b18e100 b18e43
            | (have j1 := b18e100 (σ X1) X0
               grind)
            | exact resolve b18e43 b18e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e43
          have b18e225 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b18e14 (M.op (τ X0) (τ X0))
               have i₂ := b18e72 X0
               grind)
            | exact superpose b18e72 b18e14
            | exact resolve b18e14 b18e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e72
          have b18e268 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op (M.op X0 X2) X3)) = (M.op (M.op X0 (M.op (M.op X0 X1) X1)) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b18e13 (M.op X0 X2) X3 X2
               have i₂ := b18e32 X0 X1 X2
               grind)
            | exact superpose b18e32 b18e13
            | exact resolve b18e13 b18e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e316 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X2)) = (M.op (M.op (M.op X0 X4) X4) (M.op X0 X5)) := by
            intro X0 X1 X2 X4 X5
            first
            | (have i₁ := b18e35 X0 X4 x X5
               have i₂ := b18e35 X0 X1 x X2
               grind)
            | exact superpose b18e35 b18e35
            | exact resolve b18e35 b18e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e35
          have b18e397 : ∀ X0 X1 : G, (M.op (M.op (τ X0) X1) X1) = (M.op (τ X0) (τ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b18e13 (τ X0) (τ X0) X1
               have i₂ := b18e225 X0
               grind)
            | exact superpose b18e225 b18e13
            | exact resolve b18e13 b18e225
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e416 : (M.op (σ (M.op x x)) (σ y)) = (M.op (σ x) (σ (M.op x x))) := by
            first
            | (have i₁ := b18e46 (σ x)
               have i₂ := b18e69 x
               grind)
            | exact superpose b18e69 b18e46
            | exact resolve b18e46 b18e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e752 : (M.op (σ y) (σ (k x y))) = (M.op (σ (M.op y y)) (σ y)) := by
            first
            | (have i₁ := b18e79 (σ y)
               have i₂ := b18e69 y
               grind)
            | exact superpose b18e69 b18e79
            | exact resolve b18e79 b18e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e767 : ∀ X0 : G, (M.op (M.op (σ y) X0) X0) = (M.op (σ y) (σ (M.op y x))) ∨ y = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b18e79 X0
               have i₂ := b18e100 x y
               grind)
            | exact superpose b18e100 b18e79
            | (have j1 := b18e100 x y
               grind)
            | exact resolve b18e79 b18e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e79
          have b18e817 : ∀ X0 : G, (M.op (M.op (σ y) X0) X0) = (M.op (σ y) (σ (M.op y x))) := by
            intro X0
            first
            | (have j0 := b18e767 X0
               grind)
            | (have r₁ := b18e767 X0
               have r₂ := b18e22
               grind)
            | exact resolve b18e767 b18e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e767
          have b18e882 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 (M.op X0 X1)) X2) = (M.op (M.op X0 (M.op X0 X4)) X2) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b18e36 X0 X4 X2 x
               have i₂ := b18e36 X0 X1 X2 x
               grind)
            | exact superpose b18e36 b18e36
            | exact resolve b18e36 b18e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e36
          have b18e1111 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
            intro X0
            first
            | (have j0 := b18e97 X0 (M.op X0 X0)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e97
          have b18e1112 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
            intro X0
            first
            | (have j0 := b18e1111 X0
               have j1 := b18e206 X0 x X0
               grind)
            | (have r₁ := b18e1111 x
               have r₂ := b18e206 x x x
               grind)
            | exact resolve b18e1111 b18e206
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e206 b18e1111
          have b18e1115 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ X0) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b18e1112 (σ X0)
               have i₂ := b18e69 X0
               grind)
            | exact superpose b18e69 b18e1112
            | exact resolve b18e1112 b18e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e1122 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k X0 (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b18e1115 X0
               have i₂ := b18e19 X0 (M.op X0 X0)
               grind)
            | exact superpose b18e19 b18e1115
            | exact resolve b18e1115 b18e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1115
          have b18e1126 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
            intro X0
            first
            | (have i₁ := b18e1122 X0
               have i₂ := b18e1112 X0
               grind)
            | exact superpose b18e1112 b18e1122
            | exact resolve b18e1122 b18e1112
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1112 b18e1122
          have b18e1483 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b18e159 X0 (σ X0)
               have i₂ := b18e69 X0
               grind)
            | exact superpose b18e69 b18e159
            | exact resolve b18e159 b18e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e1598 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) X0)) := by
            intro X0
            first
            | (have i₁ := b18e1483 X0
               have i₂ := b18e1126 X0
               grind)
            | exact superpose b18e1126 b18e1483
            | exact resolve b18e1483 b18e1126
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1483
          have b18e2820 : ∀ X0 X1 : G, (M.op (M.op (σ X0) X1) X1) = (σ (M.op (M.op X0 X0) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b18e163 X0 X1
               have i₂ := b18e1126 X0
               grind)
            | exact superpose b18e1126 b18e163
            | exact resolve b18e163 b18e1126
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e163 b18e1126
          have b18e3035 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (σ y)) = (M.op (σ x) (σ X0)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ X0)) ∨ (M.op (σ X0) (σ x)) = (σ (k x X0)) := by
            intro X0
            first
            | (have i₁ := b18e46 (σ X0)
               have i₂ := b18e102 X0 x
               grind)
            | exact superpose b18e102 b18e46
            | (have j1 := b18e102 X0 x
               grind)
            | exact resolve b18e46 b18e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e46
          have b18e3044 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b18e16 (σ X1) (σ X0)
               have i₂ := b18e102 X0 X1
               grind)
            | exact superpose b18e102 b18e16
            | (have j0 := b18e16 (σ X1) (σ X0)
               have j1 := b18e102 X0 X1
               grind)
            | exact resolve b18e16 b18e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e102
          have b18e3086 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b18e3044 X0 X1
               have j1 := b18e165 X1 (σ X0)
               grind)
            | (have r₁ := b18e3044 X0 X0
               have r₂ := b18e165 X0 (σ X0)
               grind)
            | exact resolve b18e3044 b18e165
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e165 b18e3044
          have b18e3094 : ∀ X0 : G, (M.op (σ (M.op x x)) (σ y)) = (M.op (σ x) (σ X0)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ X0)) ∨ (M.op (σ X0) (σ x)) = (σ (k x X0)) := by
            intro X0
            first
            | (have i₁ := b18e3035 X0
               have i₂ := b18e69 x
               grind)
            | exact superpose b18e69 b18e3035
            | (have j0 := b18e3035 X0
               grind)
            | exact resolve b18e3035 b18e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e3035
          have b18e3139 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X1 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b18e3086 X0 X1
               have i₂ := b18e69 X1
               grind)
            | exact superpose b18e69 b18e3086
            | (have j0 := b18e3086 X0 X1
               grind)
            | (have r₁ := b18e3086 (M.op X0 X0) X0
               have r₂ := b18e69 X0
               grind)
            | exact resolve b18e3086 b18e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e3086
          have b18e3146 : ∀ X0 : G, (M.op (σ x) (σ (M.op x x))) = (M.op (σ x) (σ X0)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ X0)) ∨ (M.op (σ X0) (σ x)) = (σ (k x X0)) := by
            intro X0
            first
            | (have i₁ := b18e3094 X0
               have i₂ := b18e416
               grind)
            | exact superpose b18e416 b18e3094
            | (have j0 := b18e3094 X0
               grind)
            | exact resolve b18e3094 b18e416
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e416 b18e3094
          have b18e3170 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b18e3139 X0 X1
               have i₂ := b18e19 X1 X0
               grind)
            | exact superpose b18e19 b18e3139
            | (have j0 := b18e3139 X0 X1
               grind)
            | exact resolve b18e3139 b18e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e3139
          have b18e3171 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b18e3170 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e3170
          have b18e3174 : ∀ X0 : G, (σ (M.op (M.op x x) x)) = (M.op (σ x) (σ X0)) ∨ (M.op (σ X0) (σ x)) = (σ (k x X0)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b18e3146 X0
               have i₂ := b18e1598 x
               grind)
            | exact superpose b18e1598 b18e3146
            | (have j0 := b18e3146 X0
               grind)
            | exact resolve b18e3146 b18e1598
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1598 b18e3146
          have b18e3242 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) X2) X2) = (σ (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b18e2820 X0 X2
               have i₂ := b18e34 X0 X0 X1
               grind)
            | (have i₁ := b18e2820 X0 X2
               have i₂ := b18e34 X0 X1 X0
               grind)
            | exact superpose b18e34 b18e2820
            | exact resolve b18e2820 b18e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e3243 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) X2) X2) = (σ (M.op X0 (M.op X0 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b18e2820 X0 X2
               have i₂ := b18e13 X0 X1 X0
               grind)
            | exact superpose b18e13 b18e2820
            | exact resolve b18e2820 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e3297 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (τ (M.op (M.op (σ X0) X1) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b18e14 (M.op (M.op X0 X0) X0)
               have i₂ := b18e2820 X0 X1
               grind)
            | exact superpose b18e2820 b18e14
            | exact resolve b18e14 b18e2820
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e2820
          have b18e3453 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (σ (M.op (M.op (τ X0) X2) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b18e3242 (τ X0) X2 X1
               have i₂ := b18e15 X0
               grind)
            | exact superpose b18e15 b18e3242
            | exact resolve b18e3242 b18e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e3574 : ∀ X0 : G, (M.op (σ (M.op x x)) (σ y)) = (σ (M.op (M.op x X0) X0)) := by
            intro X0
            first
            | (have i₁ := b18e152 x
               have i₂ := b18e3242 x X0 x
               grind)
            | exact superpose b18e3242 b18e152
            | exact resolve b18e152 b18e3242
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e152
          have b18e3621 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X2) = (τ (M.op (M.op (σ X0) X1) X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b18e14 (M.op (M.op X0 X2) X2)
               have i₂ := b18e3242 X0 X2 X1
               grind)
            | exact superpose b18e3242 b18e14
            | exact resolve b18e14 b18e3242
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e3764 : ∀ X0 X1 X3 : G, (σ (M.op X0 (M.op X0 X1))) = (σ (M.op X0 (M.op X0 X3))) := by
            intro X0 X1 X3
            first
            | (have i₁ := b18e3243 X0 X3 x
               have i₂ := b18e3243 X0 X1 x
               grind)
            | exact superpose b18e3243 b18e3243
            | exact resolve b18e3243 b18e3243
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e3823 : ∀ X0 X1 : G, (M.op (M.op (σ (τ X0)) X1) X1) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b18e3243 (τ X0) (τ X0) X1
               have i₂ := b18e225 X0
               grind)
            | exact superpose b18e225 b18e3243
            | exact resolve b18e3243 b18e225
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e225
          have b18e3836 : ∀ X0 : G, (M.op (σ y) (σ (M.op y x))) = (σ (M.op y (M.op y X0))) := by
            intro X0
            first
            | (have i₁ := b18e817 x
               have i₂ := b18e3243 y X0 x
               grind)
            | exact superpose b18e3243 b18e817
            | exact resolve b18e817 b18e3243
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e817
          have b18e3843 : ∀ X0 X1 X3 : G, (σ (M.op X0 (M.op X0 X1))) = (σ (M.op (M.op X0 X3) X3)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b18e3242 X0 X3 x
               have i₂ := b18e3243 X0 X1 x
               grind)
            | exact superpose b18e3243 b18e3242
            | exact resolve b18e3242 b18e3243
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e3242
          have b18e3888 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X2)) = (τ (M.op (M.op (σ X0) X1) X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b18e14 (M.op X0 (M.op X0 X2))
               have i₂ := b18e3243 X0 X2 X1
               grind)
            | exact superpose b18e3243 b18e14
            | exact resolve b18e14 b18e3243
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e3243
          have b18e3911 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b18e3823 X0 X1
               have i₂ := b18e15 X0
               grind)
            | exact superpose b18e15 b18e3823
            | exact resolve b18e3823 b18e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e3823
          have b18e4057 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X2) X2)) = (τ (M.op (M.op (σ X0) X1) X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b18e32 X0 X2 X0
               have i₂ := b18e3297 X0 X1
               grind)
            | exact superpose b18e3297 b18e32
            | exact resolve b18e32 b18e3297
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e32 b18e3297
          have b18e4310 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X2)) = (σ (M.op (M.op (τ X0) X1) X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b18e13 X0 X2 x
               have i₂ := b18e3453 X0 x X1
               grind)
            | exact superpose b18e3453 b18e13
            | exact resolve b18e13 b18e3453
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e3453
          have b18e5651 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (M.op X0 (M.op X0 X2)) X3) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b18e34 (M.op X0 (M.op X0 X2)) X3 (M.op X0 X2)
               have i₂ := b18e133 X0 (M.op X0 X2) X1 X2
               grind)
            | exact superpose b18e133 b18e34
            | exact resolve b18e34 b18e133
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e6193 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X2) = (M.op (M.op (M.op X0 X3) X3) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b18e137 X0 X3 X2 X2
               have i₂ := b18e13 X0 X1 X2
               grind)
            | exact superpose b18e13 b18e137
            | exact resolve b18e137 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e6239 : ∀ X0 X1 X2 X4 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (M.op (M.op (M.op X0 X4) X4) X2) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b18e137 X0 X4 X2 x
               have i₂ := b18e137 X0 X1 X2 x
               grind)
            | (have i₁ := b18e137 X0 X1 X2 X2
               have i₂ := b18e137 X0 X2 X2 x
               grind)
            | exact superpose b18e137 b18e137
            | exact resolve b18e137 b18e137
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e137
          have b18e8963 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X2)) = (τ (M.op (σ X0) (M.op (σ X0) X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b18e3888 X0 (M.op (σ X0) x) X2
               have i₂ := b18e205 (σ X0) x X1 x
               grind)
            | exact superpose b18e205 b18e3888
            | exact resolve b18e3888 b18e205
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e205
          have b18e15524 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b18e4310 X0 x X1
               have i₂ := b18e397 X0 x
               grind)
            | exact superpose b18e397 b18e4310
            | exact resolve b18e4310 b18e397
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e397 b18e4310
          have b18e53485 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op X0 X2) X2) (M.op X0 X3)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
            intro X0 X2 X3
            first
            | (have i₁ := b18e133 X0 X2 x X3
               have i₂ := b18e3911 X0 x
               grind)
            | exact superpose b18e3911 b18e133
            | exact resolve b18e133 b18e3911
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e133 b18e3911
          have b18e416771 : (τ (M.op (σ x) (σ x))) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b18e212 (σ x) y
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e212
            | (have j0 := b18e212 (σ x) y
               grind)
            | exact resolve b18e212 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e212
          have b18e416776 : (k y x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b18e416771
               have i₂ := b18e14 x
               grind)
            | exact superpose b18e14 b18e416771
            | exact resolve b18e416771 b18e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e416771
          have b18e416779 : (k y x) = (τ (σ (M.op x x))) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b18e416776
               have i₂ := b18e69 x
               grind)
            | exact superpose b18e69 b18e416776
            | exact resolve b18e416776 b18e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e69 b18e416776
          have b18e416781 : (M.op x x) = (k y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b18e416779
               have i₂ := b18e14 (M.op x x)
               grind)
            | exact superpose b18e14 b18e416779
            | exact resolve b18e416779 b18e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e416779
          have b18e416782 : (σ x) = (σ (k x y)) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b18e416781
               have i₂ := b18e60
               grind)
            | exact superpose b18e60 b18e416781
            | exact resolve b18e416781 b18e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e416781
          have b18e421552 : (k x y) = (τ (σ x)) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b18e14 (k x y)
               have i₂ := b18e416782
               grind)
            | exact superpose b18e416782 b18e14
            | exact resolve b18e14 b18e416782
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e416782
          have b18e421561 : (M.op x x) = (k y x) ∨ x = (k x y) := by
            first
            | (have i₁ := b18e421552
               have i₂ := b18e14 x
               grind)
            | exact superpose b18e14 b18e421552
            | exact resolve b18e421552 b18e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e421552
          have b18e423950 : (M.op x y) = (M.op x x) ∨ x = (M.op y x) ∨ x = (k x y) := by
            first
            | (have i₁ := b18e100 y x
               have i₂ := b18e421561
               grind)
            | exact superpose b18e421561 b18e100
            | (have j0 := b18e100 y x
               grind)
            | exact resolve b18e100 b18e421561
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e421561
          have b18e423951 : x = (k x y) ∨ x = (M.op y x) := by
            first
            | (have r₁ := b18e423950
               have r₂ := b18e21
               grind)
            | exact resolve b18e423950 b18e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e423950
          have b18e426418 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b18e100 x y
               have i₂ := b18e423951
               grind)
            | exact superpose b18e423951 b18e100
            | (have j0 := b18e100 y x
               grind)
            | exact resolve b18e100 b18e423951
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e100 b18e423951
          have b18e426419 : x = (M.op y x) ∨ y = (M.op x y) := by grind
          clear b18e426418
          have b18e426421 : x = (M.op y x) := by
            first
            | (have r₁ := b18e426419
               have r₂ := b18e22
               grind)
            | exact resolve b18e426419 b18e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e426419
          have b18e428969 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
            first
            | (have i₁ := b18e3836 x
               have i₂ := b18e426421
               grind)
            | exact superpose b18e426421 b18e3836
            | exact resolve b18e3836 b18e426421
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e3836
          have b18e428971 : ∀ X0 : G, (M.op x x) = (M.op y (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b18e13 y X0 x
               have i₂ := b18e426421
               grind)
            | exact superpose b18e426421 b18e13
            | exact resolve b18e13 b18e426421
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e428977 : ∀ X0 : G, (M.op x x) = (M.op (M.op y X0) X0) := by
            intro X0
            first
            | (have i₁ := b18e34 y X0 x
               have i₂ := b18e426421
               grind)
            | exact superpose b18e426421 b18e34
            | exact resolve b18e34 b18e426421
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e34
          have b18e428982 : ∀ X0 : G, (M.op y x) = (M.op y (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b18e37 y X0 x
               have i₂ := b18e426421
               grind)
            | exact superpose b18e426421 b18e37
            | exact resolve b18e37 b18e426421
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e37
          have b18e429047 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op y X0) X0) (M.op y X1)) = (M.op (M.op (M.op y X2) X2) x) := by
            intro X0 X1 X2
            first
            | (have i₁ := b18e316 y X0 X1 X2 x
               have i₂ := b18e426421
               grind)
            | exact superpose b18e426421 b18e316
            | exact resolve b18e316 b18e426421
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e316
          have b18e429134 : ∀ X0 X1 : G, (M.op (M.op y x) X1) = (M.op (M.op y (M.op y X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b18e882 y X0 X1 x
               have i₂ := b18e426421
               grind)
            | exact superpose b18e426421 b18e882
            | exact resolve b18e882 b18e426421
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e882
          have b18e429158 : ∀ X0 : G, (σ (M.op y x)) = (σ (M.op y (M.op y X0))) := by
            intro X0
            first
            | (have i₁ := b18e3764 y X0 x
               have i₂ := b18e426421
               grind)
            | exact superpose b18e426421 b18e3764
            | exact resolve b18e3764 b18e426421
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e3764
          have b18e429159 : ∀ X0 : G, (σ (M.op x x)) = (σ (M.op y (M.op y X0))) := by
            intro X0
            first
            | (have i₁ := b18e3843 y X0 x
               have i₂ := b18e426421
               grind)
            | exact superpose b18e426421 b18e3843
            | exact resolve b18e3843 b18e426421
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e3843
          have b18e429165 : ∀ X0 X1 : G, (M.op (M.op (M.op y x) X1) X1) = (M.op (M.op y X0) X0) := by
            intro X0 X1
            first
            | (have i₁ := b18e5651 y X0 x X1
               have i₂ := b18e426421
               grind)
            | exact superpose b18e426421 b18e5651
            | exact resolve b18e5651 b18e426421
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e5651
          have b18e429166 : ∀ X0 X1 : G, (M.op (M.op x x) X1) = (M.op (M.op y (M.op y X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b18e6193 y X0 X1 x
               have i₂ := b18e426421
               grind)
            | exact superpose b18e426421 b18e6193
            | exact resolve b18e6193 b18e426421
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e6193
          have b18e429168 : ∀ X0 X1 : G, (M.op (M.op x x) X1) = (M.op (M.op (M.op y X0) X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b18e6239 y X0 X1 x
               have i₂ := b18e426421
               grind)
            | exact superpose b18e426421 b18e6239
            | exact resolve b18e6239 b18e426421
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e6239
          have b18e429207 : ∀ X0 X1 : G, (M.op (M.op y X0) X0) = (M.op (M.op x X1) X1) := by
            intro X0 X1
            first
            | (have i₁ := b18e429165 X0 X1
               have i₂ := b18e426421
               grind)
            | exact superpose b18e426421 b18e429165
            | exact resolve b18e429165 b18e426421
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e429165
          have b18e429210 : (σ (M.op x x)) = (σ (M.op y x)) := by
            first
            | (have i₁ := b18e429158 x
               have i₂ := b18e429159 x
               grind)
            | exact superpose b18e429159 b18e429158
            | exact resolve b18e429158 b18e429159
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e429158 b18e429159
          have b18e429228 : ∀ X1 : G, (M.op (M.op x x) X1) = (M.op (M.op y x) X1) := by
            intro X1
            first
            | (have i₁ := b18e429134 x X1
               have i₂ := b18e429166 x X1
               grind)
            | exact superpose b18e429166 b18e429134
            | exact resolve b18e429134 b18e429166
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e429134 b18e429166
          have b18e429280 : ∀ X0 X1 : G, (M.op (M.op x x) x) = (M.op (M.op (M.op y X0) X0) (M.op y X1)) := by
            intro X0 X1
            first
            | (have i₁ := b18e429047 X0 X1 x
               have i₂ := b18e429168 x x
               grind)
            | exact superpose b18e429168 b18e429047
            | exact resolve b18e429047 b18e429168
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e429047 b18e429168
          have b18e429321 : ∀ X0 : G, x = (M.op y (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b18e428982 X0
               have i₂ := b18e426421
               grind)
            | exact superpose b18e426421 b18e428982
            | exact resolve b18e428982 b18e426421
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e428982
          have b18e429329 : (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b18e428969
               have i₂ := b18e426421
               grind)
            | exact superpose b18e426421 b18e428969
            | exact resolve b18e428969 b18e426421
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e428969
          have b18e429348 : ∀ X1 : G, (M.op x x) = (M.op (M.op x X1) X1) := by
            intro X1
            first
            | (have i₁ := b18e429207 x X1
               have i₂ := b18e428977 x
               grind)
            | exact superpose b18e428977 b18e429207
            | exact resolve b18e429207 b18e428977
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e428977 b18e429207
          have b18e429350 : (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b18e429210
               have i₂ := b18e426421
               grind)
            | exact superpose b18e426421 b18e429210
            | exact resolve b18e429210 b18e426421
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e429210
          have b18e429356 : ∀ X1 : G, (M.op (M.op x x) X1) = (M.op x X1) := by
            intro X1
            first
            | (have i₁ := b18e429228 X1
               have i₂ := b18e426421
               grind)
            | exact superpose b18e426421 b18e429228
            | exact resolve b18e429228 b18e426421
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e429228
          have b18e429394 : (M.op (M.op x x) x) = (σ (M.op (τ y) (τ (M.op y y)))) := by
            first
            | (have i₁ := b18e429280 x x
               have i₂ := b18e53485 y x x
               grind)
            | exact superpose b18e53485 b18e429280
            | exact resolve b18e429280 b18e53485
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e53485 b18e429280
          have b18e429460 : (M.op x x) = (σ (M.op (τ y) (τ (M.op y y)))) := by
            first
            | (have i₁ := b18e429394
               have i₂ := b18e429348 x
               grind)
            | exact superpose b18e429348 b18e429394
            | exact resolve b18e429394 b18e429348
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e429394
          have b18e432744 : (M.op y x) = (σ (M.op (τ y) (τ (M.op y y)))) := by
            first
            | (have i₁ := b18e15524 y (M.op y x)
               have i₂ := b18e429321 x
               grind)
            | exact superpose b18e429321 b18e15524
            | exact resolve b18e15524 b18e429321
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e15524 b18e429321
          have b18e432781 : (M.op x x) = (M.op y x) := by
            first
            | (have i₁ := b18e432744
               have i₂ := b18e429460
               grind)
            | exact superpose b18e429460 b18e432744
            | exact resolve b18e432744 b18e429460
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e429460 b18e432744
          have b18e433226 : x = (M.op x x) := by
            first
            | (have i₁ := b18e432781
               have i₂ := b18e426421
               grind)
            | exact superpose b18e426421 b18e432781
            | exact resolve b18e432781 b18e426421
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e426421 b18e432781
          have b18e436511 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b18e3574 x
               have i₂ := b18e433226
               grind)
            | exact superpose b18e433226 b18e3574
            | exact resolve b18e3574 b18e433226
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e3574
          have b18e436948 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b18e436511
               have i₂ := b18e429350
               grind)
            | exact superpose b18e429350 b18e436511
            | exact resolve b18e436511 b18e429350
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e436511
          have b18e454010 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b18e60
               have i₂ := b18e429329
               grind)
            | exact superpose b18e429329 b18e60
            | exact resolve b18e60 b18e429329
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e454049 : ∀ X0 : G, (M.op y (M.op y X0)) = (τ (M.op (σ y) (σ x))) := by
            intro X0
            first
            | (have i₁ := b18e8963 y (σ x) X0
               have i₂ := b18e429329
               grind)
            | exact superpose b18e429329 b18e8963
            | exact resolve b18e8963 b18e429329
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e8963 b18e429329
          have b18e454301 : ∀ X0 : G, (M.op y (M.op y X0)) = (τ (σ (k x y))) := by
            intro X0
            first
            | (have i₁ := b18e454049 X0
               have i₂ := b18e60
               grind)
            | exact superpose b18e60 b18e454049
            | exact resolve b18e454049 b18e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e454049
          have b18e454450 : ∀ X0 : G, (k x y) = (M.op y (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b18e454301 X0
               have i₂ := b18e14 (k x y)
               grind)
            | exact superpose b18e14 b18e454301
            | exact resolve b18e454301 b18e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e454301
          have b18e454579 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b18e454450 x
               have i₂ := b18e428971 x
               grind)
            | exact superpose b18e428971 b18e454450
            | exact resolve b18e454450 b18e428971
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e428971 b18e454450
          have b18e454677 : x = (k x y) := by
            first
            | (have i₁ := b18e454579
               have i₂ := b18e433226
               grind)
            | exact superpose b18e433226 b18e454579
            | exact resolve b18e454579 b18e433226
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e433226 b18e454579
          have b18e586777 : ∀ X0 : G, (σ X0) = (σ (M.op (M.op x x) x)) ∨ (M.op (σ X0) (σ x)) = (σ (k x X0)) ∨ (σ X0) = (σ (M.op x x)) ∨ (M.op (σ X0) (σ x)) = (σ (k x X0)) := by
            intro X0
            first
            | (have i₁ := b18e3174 X0
               have i₂ := b18e211 X0 x
               grind)
            | exact superpose b18e211 b18e3174
            | (have j0 := b18e3174 X0
               have j1 := b18e211 X0 x
               grind)
            | exact resolve b18e3174 b18e211
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e211 b18e3174
          have b18e587651 : ∀ X0 : G, (σ X0) = (σ (M.op (M.op x x) x)) ∨ (M.op (σ X0) (σ x)) = (σ (k x X0)) ∨ (σ X0) = (σ (M.op x x)) := by
            intro X0
            first
            | (have j0 := b18e586777 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e586777
          have b18e587653 : ∀ X0 : G, (σ X0) = (σ (M.op (M.op x x) x)) ∨ (M.op (σ X0) (σ x)) = (σ (k x X0)) := by
            intro X0
            first
            | (have j0 := b18e587651 X0
               have j1 := b18e3171 X0 x
               grind)
            | (have r₁ := b18e587651 (M.op x x)
               have r₂ := b18e3171 (M.op (M.op x x) x) x
               grind)
            | (have r₁ := b18e587651 X0
               have r₂ := b18e3171 X0 x
               grind)
            | (have r₁ := b18e587651 (M.op x x)
               have r₂ := b18e3171 (M.op x x) x
               grind)
            | exact resolve b18e587651 b18e3171
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e587651
          have b18e587654 : ∀ X0 : G, (σ X0) = (σ (M.op x x)) ∨ (M.op (σ X0) (σ x)) = (σ (k x X0)) := by
            intro X0
            first
            | (have i₁ := b18e587653 X0
               have i₂ := b18e429348 x
               grind)
            | exact superpose b18e429348 b18e587653
            | (have j0 := b18e587653 X0
               grind)
            | exact resolve b18e587653 b18e429348
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e429348 b18e587653
          have b18e587655 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (k x X0)) := by
            intro X0
            first
            | (have j0 := b18e587654 X0
               have j1 := b18e3171 X0 x
               grind)
            | (have r₁ := b18e587654 X0
               have r₂ := b18e3171 X0 x
               grind)
            | (have r₁ := b18e587654 (M.op x x)
               have r₂ := b18e3171 (M.op x x) x
               grind)
            | exact resolve b18e587654 b18e3171
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e3171 b18e587654
          have b18e587816 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (k x X0)) (σ x)) := by
            intro X0
            first
            | (have i₁ := b18e159 X0 (σ x)
               have i₂ := b18e587655 X0
               grind)
            | exact superpose b18e587655 b18e159
            | exact resolve b18e159 b18e587655
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e159
          have b18e587826 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (τ (M.op (σ (k x X0)) (σ x))) := by
            intro X0 X1
            first
            | (have i₁ := b18e3621 X0 (σ x) X1
               have i₂ := b18e587655 X0
               grind)
            | exact superpose b18e587655 b18e3621
            | exact resolve b18e3621 b18e587655
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e3621
          have b18e587828 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (τ (M.op (σ (k x X0)) (σ x))) := by
            intro X0 X1
            first
            | (have i₁ := b18e3888 X0 (σ x) X1
               have i₂ := b18e587655 X0
               grind)
            | exact superpose b18e587655 b18e3888
            | exact resolve b18e3888 b18e587655
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e3888
          have b18e587833 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) X1)) = (τ (M.op (σ (k x X0)) (σ x))) := by
            intro X0 X1
            first
            | (have i₁ := b18e4057 X0 (σ x) X1
               have i₂ := b18e587655 X0
               grind)
            | exact superpose b18e587655 b18e4057
            | exact resolve b18e4057 b18e587655
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e4057
          have b18e588094 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) X1)) = (τ (σ (k x (k x X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b18e587833 X0 X1
               have i₂ := b18e587655 (k x X0)
               grind)
            | exact superpose b18e587655 b18e587833
            | exact resolve b18e587833 b18e587655
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e587833
          have b18e588098 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (τ (σ (k x (k x X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b18e587828 X0 X1
               have i₂ := b18e587655 (k x X0)
               grind)
            | exact superpose b18e587655 b18e587828
            | exact resolve b18e587828 b18e587655
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e587828
          have b18e588099 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (τ (σ (k x (k x X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b18e587826 X0 X1
               have i₂ := b18e587655 (k x X0)
               grind)
            | exact superpose b18e587655 b18e587826
            | exact resolve b18e587826 b18e587655
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e587826
          have b18e588105 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k x (k x X0))) := by
            intro X0
            first
            | (have i₁ := b18e587816 X0
               have i₂ := b18e587655 (k x X0)
               grind)
            | exact superpose b18e587655 b18e587816
            | exact resolve b18e587816 b18e587655
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e587655 b18e587816
          have b18e588265 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) X1)) = (k x (k x X0)) := by
            intro X0 X1
            first
            | (have i₁ := b18e588094 X0 X1
               have i₂ := b18e14 (k x (k x X0))
               grind)
            | exact superpose b18e14 b18e588094
            | exact resolve b18e588094 b18e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e588094
          have b18e588269 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k x (k x X0)) := by
            intro X0 X1
            first
            | (have i₁ := b18e588098 X0 X1
               have i₂ := b18e14 (k x (k x X0))
               grind)
            | exact superpose b18e14 b18e588098
            | exact resolve b18e588098 b18e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e588098
          have b18e588270 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (k x (k x X0)) := by
            intro X0 X1
            first
            | (have i₁ := b18e588099 X0 X1
               have i₂ := b18e14 (k x (k x X0))
               grind)
            | exact superpose b18e14 b18e588099
            | exact resolve b18e588099 b18e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e588099
          have b18e602363 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op (M.op X0 X3) X3)) X1) = (k x (k x (M.op X0 X1))) := by
            intro X0 X1 X3
            first
            | (have i₁ := b18e268 X0 X3 X1 x
               have i₂ := b18e588269 (M.op X0 X1) x
               grind)
            | exact superpose b18e588269 b18e268
            | exact resolve b18e268 b18e588269
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e268
          have b18e602396 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k x (k x (σ X0))) := by
            intro X0
            first
            | (have i₁ := b18e192 X0 x
               have i₂ := b18e588269 (σ X0) x
               grind)
            | exact superpose b18e588269 b18e192
            | exact resolve b18e192 b18e588269
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e192 b18e588269
          have b18e602628 : ∀ X0 : G, (σ (k x (k x X0))) = (k x (k x (σ X0))) := by
            intro X0
            first
            | (have i₁ := b18e602396 X0
               have i₂ := b18e588105 X0
               grind)
            | exact superpose b18e588105 b18e602396
            | exact resolve b18e602396 b18e588105
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e588105 b18e602396
          have b18e602643 : ∀ X0 X1 : G, (M.op (k x (k x X0)) X1) = (k x (k x (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b18e602363 X0 X1 x
               have i₂ := b18e588265 X0 x
               grind)
            | exact superpose b18e588265 b18e602363
            | exact resolve b18e602363 b18e588265
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e588265 b18e602363
          have b18e606932 : (M.op (M.op (σ y) (σ (k x y))) (σ y)) = (k x (k x (σ (M.op y y)))) := by
            first
            | (have i₁ := b18e588270 (σ (M.op y y)) (σ y)
               have i₂ := b18e752
               grind)
            | exact superpose b18e752 b18e588270
            | exact resolve b18e588270 b18e752
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e752 b18e588270
          have b18e607868 : (M.op (M.op (σ y) (σ (k x y))) (σ y)) = (σ (k x (k x (M.op y y)))) := by
            first
            | (have i₁ := b18e606932
               have i₂ := b18e602628 (M.op y y)
               grind)
            | exact superpose b18e602628 b18e606932
            | exact resolve b18e606932 b18e602628
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e602628 b18e606932
          have b18e608154 : (M.op (M.op (σ y) (σ (k x y))) (σ y)) = (σ (M.op (k x (k x y)) y)) := by
            first
            | (have i₁ := b18e607868
               have i₂ := b18e602643 y y
               grind)
            | exact superpose b18e602643 b18e607868
            | exact resolve b18e607868 b18e602643
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e602643 b18e607868
          have b18e608305 : (M.op (M.op (σ y) (σ x)) (σ y)) = (σ (M.op (k x x) y)) := by
            first
            | (have i₁ := b18e608154
               have i₂ := b18e454677
               grind)
            | exact superpose b18e454677 b18e608154
            | exact resolve b18e608154 b18e454677
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e454677 b18e608154
          have b18e608399 : (M.op (M.op (σ y) (σ x)) (σ y)) = (σ (M.op (M.op x x) y)) := by
            first
            | (have i₁ := b18e608305
               have i₂ := b18e58 x
               grind)
            | exact superpose b18e58 b18e608305
            | exact resolve b18e608305 b18e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e58 b18e608305
          have b18e608459 : (σ (M.op x y)) = (M.op (M.op (σ y) (σ x)) (σ y)) := by
            first
            | (have i₁ := b18e608399
               have i₂ := b18e429356 y
               grind)
            | exact superpose b18e429356 b18e608399
            | exact resolve b18e608399 b18e429356
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e429356 b18e608399
          have b18e608500 : (σ (M.op x y)) = (M.op (σ (k x y)) (σ y)) := by
            first
            | (have i₁ := b18e608459
               have i₂ := b18e60
               grind)
            | exact superpose b18e60 b18e608459
            | exact resolve b18e608459 b18e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e60 b18e608459
          have b18e608532 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b18e608500
               have i₂ := b18e454010
               grind)
            | exact superpose b18e454010 b18e608500
            | exact resolve b18e608500 b18e454010
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e454010 b18e608500
          have b18e608549 : (σ (M.op x y)) = (σ x) := by
            first
            | (have i₁ := b18e608532
               have i₂ := b18e436948
               grind)
            | exact superpose b18e436948 b18e608532
            | exact resolve b18e608532 b18e436948
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e436948 b18e608532
          have b18e612733 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b18e158
               have i₂ := b18e608549
               grind)
            | exact superpose b18e608549 b18e158
            | exact resolve b18e158 b18e608549
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e158 b18e608549
          have b18e612836 : False := by grind
          exact b18e612836
        · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
          · have b19e25 : (M.op x x) ≠ (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e27 : False := by grind
            exact b19e27
          · have b20e25 : (M.op x x) ≠ (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e27 : False := by grind
            exact b20e27
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op x x) (M.op x x) with h2a | h2a
          · have b21e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X2) := by
              intro X0 X1 X2
              grind
            have b21e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b21e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
              intro X0 X1
              grind
            have b21e18 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b21e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              grind
            have b21e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b21e22 : (M.op x y) ≠ (M.op x x) := by grind
            have b21e23 : y ≠ (M.op x y) := by grind
            have b21e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
            have b21e25 : (σ y) = (M.op (σ x) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e27 : (σ y) ≠ (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b21e24
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e24
              | exact resolve b21e24 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e35 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) X0) X0) := by
              intro X0
              first
              | (have i₁ := b21e14 (σ x) (σ y) X0
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e14
              | exact resolve b21e14 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e36 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) X3) = (M.op X0 (M.op (M.op X0 X1) X1)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b21e14 X0 (M.op X0 x) X3
                 have i₂ := b21e14 X0 x X1
                 grind)
              | exact superpose b21e14 b21e14
              | exact resolve b21e14 b21e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e38 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X3) X3) := by
              intro X0 X1 X3
              first
              | (have i₁ := b21e14 X0 x X3
                 have i₂ := b21e14 X0 x X1
                 grind)
              | exact superpose b21e14 b21e14
              | exact resolve b21e14 b21e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e43 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) X0) := by
              intro X0
              first
              | (have i₁ := b21e35 X0
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e35
              | exact resolve b21e35 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e35
            have b21e44 : (σ y) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b21e43 (σ y)
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e43
              | exact resolve b21e43 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e43
            have b21e53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
              intro X0
              first
              | (have j0 := b21e17 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e55 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have i₁ := b21e20 X0 X0
                 have i₂ := b21e53 (σ X0)
                 grind)
              | exact superpose b21e53 b21e20
              | exact resolve b21e20 b21e53
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e58 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b21e55 X0
                 have i₂ := b21e53 X0
                 grind)
              | exact superpose b21e53 b21e55
              | exact resolve b21e55 b21e53
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e55
            have b21e61 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b21e18 (σ x) (σ y)
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e18
              | (have j0 := b21e18 (σ x) (σ y)
                 grind)
              | (have r₁ := b21e18 (σ x) (σ y)
                 have r₂ := b21e25
                 grind)
              | exact resolve b21e18 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e65 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
            clear b21e61
            have b21e66 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b21e65
                 have r₂ := b21e27
                 grind)
              | exact resolve b21e65 b21e27
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e27 b21e65
            have b21e67 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b21e66
                 have i₂ := b21e20 x y
                 grind)
              | exact superpose b21e20 b21e66
              | exact resolve b21e66 b21e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e66
            have b21e68 : (σ (k x y)) = (σ (M.op x x)) := by
              first
              | (have i₁ := b21e67
                 have i₂ := b21e58 x
                 grind)
              | exact superpose b21e58 b21e67
              | exact resolve b21e67 b21e58
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e58 b21e67
            have b21e69 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
              first
              | (have i₁ := b21e17 (σ y) (σ y)
                 have i₂ := b21e44
                 grind)
              | exact superpose b21e44 b21e17
              | exact resolve b21e17 b21e44
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e44
            have b21e73 : (σ y) = (k (σ y) (σ y)) := by grind
            clear b21e69
            have b21e76 : (σ y) = (σ (k y y)) := by
              first
              | (have i₁ := b21e73
                 have i₂ := b21e20 y y
                 grind)
              | exact superpose b21e20 b21e73
              | exact resolve b21e73 b21e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e73
            have b21e77 : (σ y) = (σ (M.op y y)) := by
              first
              | (have i₁ := b21e76
                 have i₂ := b21e53 y
                 grind)
              | exact superpose b21e53 b21e76
              | exact resolve b21e76 b21e53
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e53 b21e76
            have b21e105 : (M.op y y) = (τ (σ y)) := by
              first
              | (have i₁ := b21e15 (M.op y y)
                 have i₂ := b21e77
                 grind)
              | exact superpose b21e77 b21e15
              | exact resolve b21e15 b21e77
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e77
            have b21e106 : y = (M.op y y) := by
              first
              | (have i₁ := b21e105
                 have i₂ := b21e15 y
                 grind)
              | exact superpose b21e15 b21e105
              | exact resolve b21e105 b21e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e105
            have b21e112 : (k x y) = (τ (σ (M.op x x))) := by
              first
              | (have i₁ := b21e15 (k x y)
                 have i₂ := b21e68
                 grind)
              | exact superpose b21e68 b21e15
              | exact resolve b21e15 b21e68
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e68
            have b21e113 : (M.op x x) = (k x y) := by
              first
              | (have i₁ := b21e112
                 have i₂ := b21e15 (M.op x x)
                 grind)
              | exact superpose b21e15 b21e112
              | exact resolve b21e112 b21e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e112
            have b21e137 : (M.op x x) = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
              first
              | (have i₁ := b21e19 x y
                 have i₂ := b21e113
                 grind)
              | exact superpose b21e113 b21e19
              | (have j0 := b21e19 x y
                 grind)
              | exact resolve b21e19 b21e113
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e113
            have b21e138 : (M.op x x) = (M.op y x) ∨ y = (M.op x y) := by
              first
              | (have r₁ := b21e137
                 have r₂ := b21e22
                 grind)
              | exact resolve b21e137 b21e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e137
            have b21e140 : (M.op x x) = (M.op y x) := by
              first
              | (have r₁ := b21e138
                 have r₂ := b21e23
                 grind)
              | exact resolve b21e138 b21e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e138
            have b21e165 : ∀ X0 : G, (M.op y y) = (M.op (M.op y X0) X0) := by
              intro X0
              first
              | (have i₁ := b21e38 y X0 y
                 have i₂ := b21e106
                 grind)
              | exact superpose b21e106 b21e38
              | exact resolve b21e38 b21e106
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e180 : ∀ X0 : G, y = (M.op (M.op y X0) X0) := by
              intro X0
              first
              | (have i₁ := b21e165 X0
                 have i₂ := b21e106
                 grind)
              | exact superpose b21e106 b21e165
              | exact resolve b21e165 b21e106
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e106 b21e165
            have b21e189 : ∀ X0 : G, (M.op (M.op y X0) X0) = (M.op (M.op x x) x) := by
              intro X0
              first
              | (have i₁ := b21e38 y X0 x
                 have i₂ := b21e140
                 grind)
              | exact superpose b21e140 b21e38
              | exact resolve b21e38 b21e140
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e140
            have b21e190 : y = (M.op (M.op x x) x) := by
              first
              | (have i₁ := b21e189 x
                 have i₂ := b21e180 x
                 grind)
              | exact superpose b21e180 b21e189
              | exact resolve b21e189 b21e180
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e180 b21e189
            have b21e261 : ∀ X0 : G, y = (M.op (M.op x X0) X0) := by
              intro X0
              first
              | (have i₁ := b21e38 x x X0
                 have i₂ := b21e190
                 grind)
              | exact superpose b21e190 b21e38
              | exact resolve b21e38 b21e190
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e38
            have b21e332 : ∀ X0 : G, (M.op x y) = (M.op (M.op x X0) X0) := by
              intro X0
              first
              | (have i₁ := b21e36 x x X0
                 have i₂ := b21e190
                 grind)
              | exact superpose b21e190 b21e36
              | exact resolve b21e36 b21e190
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e36 b21e190
            have b21e357 : y = (M.op x y) := by
              first
              | (have i₁ := b21e332 x
                 have i₂ := b21e261 x
                 grind)
              | exact superpose b21e261 b21e332
              | exact resolve b21e332 b21e261
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e261 b21e332
            have b21e367 : False := by grind
            exact b21e367
          · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
            · have b22e27 : (M.op x x) ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e29 : False := by grind
              exact b22e29
            · have b23e27 : (M.op x x) ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e29 : False := by grind
              exact b23e29
        · rcases eq_or_ne (M.op x x) (M.op x x) with h2a | h2a
          · have b24e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X2) := by
              intro X0 X1 X2
              grind
            have b24e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b24e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b24e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
              intro X0 X1
              grind
            have b24e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              grind
            have b24e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b24e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b24e20 (τ X0) X1
                 have i₂ := b24e16 X0
                 grind)
              | exact superpose b24e16 b24e20
              | exact resolve b24e20 b24e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e28 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b24e20 X1 (τ X0)
                 have i₂ := b24e16 X0
                 grind)
              | exact superpose b24e16 b24e20
              | exact resolve b24e20 b24e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e31 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X3) X3) := by
              intro X0 X1 X3
              first
              | (have i₁ := b24e14 X0 x X3
                 have i₂ := b24e14 X0 x X1
                 grind)
              | exact superpose b24e14 b24e14
              | exact resolve b24e14 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op (M.op X0 X2) X3)) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b24e14 (M.op X0 X2) X3 X2
                 have i₂ := b24e14 X0 X1 X2
                 grind)
              | exact superpose b24e14 b24e14
              | exact resolve b24e14 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e34 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e14 X0 X1 x
                 have i₂ := b24e14 X0 X2 x
                 grind)
              | exact superpose b24e14 b24e14
              | exact resolve b24e14 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e48 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
              intro X0
              first
              | (have j0 := b24e17 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e50 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have i₁ := b24e20 X0 X0
                 have i₂ := b24e48 (σ X0)
                 grind)
              | exact superpose b24e48 b24e20
              | exact resolve b24e20 b24e48
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e52 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
              intro X0
              first
              | (have i₁ := b24e28 X0 (τ X0)
                 have i₂ := b24e48 (τ X0)
                 grind)
              | exact superpose b24e48 b24e28
              | exact resolve b24e28 b24e48
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e28
            have b24e53 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
              intro X0
              first
              | (have i₁ := b24e52 X0
                 have i₂ := b24e16 X0
                 grind)
              | exact superpose b24e16 b24e52
              | exact resolve b24e52 b24e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e52
            have b24e55 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b24e50 X0
                 have i₂ := b24e48 X0
                 grind)
              | exact superpose b24e48 b24e50
              | exact resolve b24e50 b24e48
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e50
            have b24e57 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
              intro X0
              first
              | (have i₁ := b24e53 X0
                 have i₂ := b24e48 X0
                 grind)
              | exact superpose b24e48 b24e53
              | exact resolve b24e53 b24e48
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e48 b24e53
            have b24e75 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1
              first
              | (have i₁ := b24e20 X1 X0
                 have i₂ := b24e19 (σ X1) (σ X0)
                 grind)
              | exact superpose b24e19 b24e20
              | (have j1 := b24e19 (σ X1) (σ X0)
                 grind)
              | exact resolve b24e20 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e79 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b24e17 X0 X1
                 have i₂ := b24e19 X0 X1
                 grind)
              | (have i₁ := b24e17 X0 X0
                 have i₂ := b24e19 X0 X1
                 grind)
              | exact superpose b24e19 b24e17
              | (have j0 := b24e17 X0 X0
                 have j1 := b24e19 X0 X1
                 grind)
              | (have r₁ := b24e17 X0 X1
                 have r₂ := b24e19 X0 X1
                 grind)
              | (have r₁ := b24e17 X1 X1
                 have r₂ := b24e19 X1 X1
                 grind)
              | (have r₁ := b24e17 X0 (M.op X0 X0)
                 have r₂ := b24e19 X0 (M.op X0 X0)
                 grind)
              | exact resolve b24e17 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e88 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              first
              | (have j0 := b24e79 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e79
            have b24e89 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              first
              | (have j0 := b24e88 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e88
            have b24e91 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1
              first
              | (have i₁ := b24e75 X0 X1
                 have i₂ := b24e55 X1
                 grind)
              | exact superpose b24e55 b24e75
              | (have j0 := b24e75 X0 X1
                 grind)
              | exact resolve b24e75 b24e55
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e75
            have b24e124 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X2) X3) X3) = (M.op (M.op (M.op X0 X1) X1) X2) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b24e31 (M.op X0 X2) X3 X2
                 have i₂ := b24e31 X0 X2 X1
                 grind)
              | (have i₁ := b24e31 (M.op X0 X2) X3 X2
                 have i₂ := b24e31 X0 X1 X2
                 grind)
              | exact superpose b24e31 b24e31
              | exact resolve b24e31 b24e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e125 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X2) X3) X3) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b24e31 (M.op X0 X2) X3 X2
                 have i₂ := b24e14 X0 X1 X2
                 grind)
              | exact superpose b24e14 b24e31
              | exact resolve b24e31 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e141 : ∀ X0 X1 : G, (M.op (M.op (σ X0) X1) X1) = (M.op (σ X0) (σ (M.op X0 X0))) := by
              intro X0 X1
              first
              | (have i₁ := b24e14 (σ X0) (σ X0) X1
                 have i₂ := b24e55 X0
                 grind)
              | exact superpose b24e55 b24e14
              | exact resolve b24e14 b24e55
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e145 : ∀ X0 X1 : G, (M.op (M.op (σ X0) X1) X1) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
              intro X0 X1
              first
              | (have i₁ := b24e31 (σ X0) X1 (σ X0)
                 have i₂ := b24e55 X0
                 grind)
              | exact superpose b24e55 b24e31
              | exact resolve b24e31 b24e55
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e31
            have b24e147 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
              intro X0 X1
              first
              | (have i₁ := b24e17 (σ X0) X1
                 have i₂ := b24e55 X0
                 grind)
              | exact superpose b24e55 b24e17
              | (have j0 := b24e17 (σ X0) X1
                 grind)
              | exact resolve b24e17 b24e55
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e170 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ X0) (M.op (σ X0) X1)) := by
              intro X0 X1
              first
              | (have i₁ := b24e34 (σ X0) X1 (σ X0)
                 have i₂ := b24e55 X0
                 grind)
              | exact superpose b24e55 b24e34
              | exact resolve b24e34 b24e55
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e183 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X2)) = (M.op (M.op X0 (M.op X0 X1)) (M.op X0 X3)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b24e14 X0 X2 (M.op X0 X3)
                 have i₂ := b24e34 X0 X3 X1
                 grind)
              | (have i₁ := b24e14 X0 X2 (M.op X0 X3)
                 have i₂ := b24e34 X0 X1 X3
                 grind)
              | exact superpose b24e34 b24e14
              | exact resolve b24e14 b24e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e197 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b24e15 (M.op (τ X0) (τ X0))
                 have i₂ := b24e57 X0
                 grind)
              | exact superpose b24e57 b24e15
              | exact resolve b24e15 b24e57
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e204 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1
              first
              | (have i₁ := b24e20 X1 X0
                 have i₂ := b24e89 (σ X1) (σ X0)
                 grind)
              | exact superpose b24e89 b24e20
              | (have j1 := b24e89 (σ X1) (σ X0)
                 grind)
              | exact resolve b24e20 b24e89
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e206 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b24e27 X1 X0
                 have i₂ := b24e89 (τ X1) X0
                 grind)
              | exact superpose b24e89 b24e27
              | (have j1 := b24e89 (τ X1) X0
                 grind)
              | exact resolve b24e27 b24e89
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e89
            have b24e283 : ∀ X0 X1 : G, (M.op (M.op (τ X0) X1) X1) = (M.op (τ X0) (τ (M.op X0 X0))) := by
              intro X0 X1
              first
              | (have i₁ := b24e14 (τ X0) (τ X0) X1
                 have i₂ := b24e197 X0
                 grind)
              | exact superpose b24e197 b24e14
              | exact resolve b24e14 b24e197
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e291 : ∀ X0 X1 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (M.op (τ X0) (M.op (τ X0) X1)) := by
              intro X0 X1
              first
              | (have i₁ := b24e34 (τ X0) X1 (τ X0)
                 have i₂ := b24e197 X0
                 grind)
              | exact superpose b24e197 b24e34
              | exact resolve b24e34 b24e197
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e34 b24e197
            have b24e704 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 (M.op X0 X1)) X2) = (M.op (M.op X0 (M.op X0 X4)) X2) := by
              intro X0 X1 X2 X4
              first
              | (have i₁ := b24e33 X0 X4 X2 x
                 have i₂ := b24e33 X0 X1 X2 x
                 grind)
              | exact superpose b24e33 b24e33
              | exact resolve b24e33 b24e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e33
            have b24e1976 : ∀ X0 X1 X2 : G, (M.op (σ X1) (σ X0)) = (M.op (M.op (σ X1) X2) X2) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e14 (σ X1) (σ X0) X2
                 have i₂ := b24e91 X0 X1
                 grind)
              | exact superpose b24e91 b24e14
              | (have j1 := b24e91 X0 X1
                 grind)
              | exact resolve b24e14 b24e91
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e1978 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b24e17 (σ X1) (σ X0)
                 have i₂ := b24e91 X0 X1
                 grind)
              | exact superpose b24e91 b24e17
              | (have j0 := b24e17 (σ X1) (σ X0)
                 have j1 := b24e91 X0 X1
                 grind)
              | exact resolve b24e17 b24e91
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e91
            have b24e2018 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have j0 := b24e1978 X0 X1
                 have j1 := b24e147 X1 (σ X0)
                 grind)
              | (have r₁ := b24e1978 X0 X0
                 have r₂ := b24e147 X0 (σ X0)
                 grind)
              | exact resolve b24e1978 b24e147
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e147 b24e1978
            have b24e2047 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X1 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b24e2018 X0 X1
                 have i₂ := b24e55 X1
                 grind)
              | exact superpose b24e55 b24e2018
              | (have j0 := b24e2018 X0 X1
                 grind)
              | (have r₁ := b24e2018 (M.op X0 X0) X0
                 have r₂ := b24e55 X0
                 grind)
              | exact resolve b24e2018 b24e55
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e2018
            have b24e2065 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b24e2047 X0 X1
                 have i₂ := b24e20 X1 X0
                 grind)
              | exact superpose b24e20 b24e2047
              | (have j0 := b24e2047 X0 X1
                 grind)
              | exact resolve b24e2047 b24e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e2047
            have b24e2066 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have j0 := b24e2065 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e2065
            have b24e2422 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X2) = (M.op (M.op (M.op X0 X3) X3) X2) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b24e124 X0 X3 X2 X2
                 have i₂ := b24e14 X0 X1 X2
                 grind)
              | exact superpose b24e14 b24e124
              | exact resolve b24e124 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e2706 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (M.op X0 X0)) X1) X1) = (M.op (M.op (σ X0) (M.op (σ X0) X2)) (σ X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e125 (σ X0) X2 (σ X0) X1
                 have i₂ := b24e55 X0
                 grind)
              | exact superpose b24e55 b24e125
              | exact resolve b24e125 b24e55
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e55 b24e125
            have b24e4650 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b24e206 X0 (σ X0)
                 have i₂ := b24e15 X0
                 grind)
              | exact superpose b24e15 b24e206
              | exact resolve b24e206 b24e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e206
            have b24e4723 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b24e4650 X0 X1
                 have i₂ := b24e20 X0 X1
                 grind)
              | exact superpose b24e20 b24e4650
              | (have j0 := b24e4650 X0 X1
                 grind)
              | exact resolve b24e4650 b24e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e4650
            have b24e20560 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k X0 (M.op X0 X0))) := by
              intro X0
              first
              | (have j0 := b24e2066 (M.op X0 X0) X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e20607 : ∀ X0 : G, (M.op (σ (M.op (τ X0) (τ X0))) X0) = (σ (k (τ X0) (M.op (τ X0) (τ X0)))) := by
              intro X0
              first
              | (have i₁ := b24e20560 (τ X0)
                 have i₂ := b24e16 X0
                 grind)
              | exact superpose b24e16 b24e20560
              | exact resolve b24e20560 b24e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e20620 : ∀ X0 X1 : G, (M.op (M.op (σ X0) X1) X1) = (σ (k X0 (M.op X0 X0))) := by
              intro X0 X1
              first
              | (have i₁ := b24e145 X0 X1
                 have i₂ := b24e20560 X0
                 grind)
              | exact superpose b24e20560 b24e145
              | exact resolve b24e145 b24e20560
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e145 b24e20560
            have b24e20747 : ∀ X0 : G, (M.op (σ (M.op (τ X0) (τ X0))) X0) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
              intro X0
              first
              | (have i₁ := b24e20607 X0
                 have i₂ := b24e27 X0 (M.op (τ X0) (τ X0))
                 grind)
              | exact superpose b24e27 b24e20607
              | exact resolve b24e20607 b24e27
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e20607
            have b24e20797 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b24e20747 X0
                 have i₂ := b24e57 X0
                 grind)
              | exact superpose b24e57 b24e20747
              | exact resolve b24e20747 b24e57
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e20747
            have b24e22331 : ∀ X0 X1 : G, (M.op (M.op (σ X0) X1) X1) = (σ (M.op (M.op X0 X0) X0)) := by
              intro X0 X1
              first
              | (have i₁ := b24e20620 X0 X1
                 have i₂ := b24e20797 X0
                 grind)
              | exact superpose b24e20797 b24e20620
              | exact resolve b24e20620 b24e20797
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e20797
            have b24e22508 : ∀ X0 X1 : G, (M.op (M.op (σ (τ X0)) X1) X1) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
              intro X0 X1
              first
              | (have i₁ := b24e27 X0 (M.op (τ X0) (τ X0))
                 have i₂ := b24e20620 (τ X0) X1
                 grind)
              | exact superpose b24e20620 b24e27
              | exact resolve b24e27 b24e20620
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e22580 : ∀ X0 X1 : G, (M.op (M.op (σ (τ X0)) X1) X1) = (k X0 (M.op X0 X0)) := by
              intro X0 X1
              first
              | (have i₁ := b24e22508 X0 X1
                 have i₂ := b24e57 X0
                 grind)
              | exact superpose b24e57 b24e22508
              | exact resolve b24e22508 b24e57
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e57 b24e22508
            have b24e22827 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (k X0 (M.op X0 X0)) := by
              intro X0 X1
              first
              | (have i₁ := b24e22580 X0 X1
                 have i₂ := b24e16 X0
                 grind)
              | exact superpose b24e16 b24e22580
              | exact resolve b24e22580 b24e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e22580
            have b24e23899 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 X0)) := by
              intro X0 X1
              first
              | (have i₁ := b24e183 X0 x X1 x
                 have i₂ := b24e22827 X0 (M.op X0 x)
                 grind)
              | exact superpose b24e22827 b24e183
              | exact resolve b24e183 b24e22827
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e183 b24e22827
            have b24e25731 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) X2) X2) = (σ (M.op X0 (M.op X0 X1))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e20620 X0 X2
                 have i₂ := b24e23899 X0 X1
                 grind)
              | exact superpose b24e23899 b24e20620
              | exact resolve b24e20620 b24e23899
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e20620 b24e23899
            have b24e27118 : ∀ X0 X1 X2 X3 : G, (σ (M.op (M.op (M.op X0 X1) X1) X2)) = (M.op (M.op (σ (M.op X0 X2)) X3) X3) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b24e22331 (M.op X0 X2) X3
                 have i₂ := b24e124 X0 X1 X2 (M.op X0 X2)
                 grind)
              | exact superpose b24e124 b24e22331
              | exact resolve b24e22331 b24e124
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e124
            have b24e27314 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (τ (M.op (M.op (σ X0) X1) X1)) := by
              intro X0 X1
              first
              | (have i₁ := b24e15 (M.op (M.op X0 X0) X0)
                 have i₂ := b24e22331 X0 X1
                 grind)
              | exact superpose b24e22331 b24e15
              | exact resolve b24e15 b24e22331
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e22331
            have b24e36656 : ∀ X0 X1 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (τ (M.op (M.op (σ (τ X0)) X1) X1)) := by
              intro X0 X1
              first
              | (have i₁ := b24e283 X0 (τ X0)
                 have i₂ := b24e27314 (τ X0) X1
                 grind)
              | exact superpose b24e27314 b24e283
              | exact resolve b24e283 b24e27314
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e283 b24e27314
            have b24e36823 : ∀ X0 X1 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (τ (M.op (M.op X0 X1) X1)) := by
              intro X0 X1
              first
              | (have i₁ := b24e36656 X0 X1
                 have i₂ := b24e16 X0
                 grind)
              | exact superpose b24e16 b24e36656
              | exact resolve b24e36656 b24e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e36656
            have b24e42674 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X1))) := by
              intro X0 X1
              first
              | (have i₁ := b24e141 X0 x
                 have i₂ := b24e25731 X0 X1 x
                 grind)
              | exact superpose b24e25731 b24e141
              | exact resolve b24e141 b24e25731
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e141 b24e25731
            have b24e121428 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X1) X1)) = (M.op (τ X0) (τ (M.op (M.op X0 X1) X1))) := by
              intro X0 X1
              first
              | (have i₁ := b24e291 X0 (τ (M.op X0 X0))
                 have i₂ := b24e36823 X0 X1
                 grind)
              | exact superpose b24e36823 b24e291
              | exact resolve b24e291 b24e36823
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e291 b24e36823
            have b24e132002 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X1))) = (M.op (σ X0) (σ (M.op X0 (M.op X0 X1)))) := by
              intro X0 X1
              first
              | (have i₁ := b24e170 X0 (σ (M.op X0 X0))
                 have i₂ := b24e42674 X0 X1
                 grind)
              | exact superpose b24e42674 b24e170
              | exact resolve b24e170 b24e42674
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e170 b24e42674
            have b24e435149 : ∀ X0 X1 X2 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (M.op (σ X1) X2) X2) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e1976 X0 X1 X2
                 have i₂ := b24e204 X0 X1
                 grind)
              | exact superpose b24e204 b24e1976
              | (have j0 := b24e1976 X0 X1 X2
                 have j1 := b24e204 X0 X1
                 grind)
              | exact resolve b24e1976 b24e204
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e204 b24e1976
            have b24e437248 : ∀ X0 X1 X2 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (M.op (σ X1) X2) X2) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1 X2
              first
              | (have j0 := b24e435149 X0 X1 X2
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e435149
            have b24e437253 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ X1) X2) X2) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1 X2
              first
              | (have j0 := b24e437248 X0 X1 X2
                 have j1 := b24e2066 X0 X1
                 grind)
              | (have r₁ := b24e437248 X0 X1 X2
                 have r₂ := b24e2066 X0 X1
                 grind)
              | (have r₁ := b24e437248 (M.op X1 X1) X1 X2
                 have r₂ := b24e2066 (M.op X1 X1) X1
                 grind)
              | exact resolve b24e437248 b24e2066
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e2066 b24e437248
            have b24e762277 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (M.op (M.op X0 X2) X2) = (σ X1) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e437253 X0 (τ X0) X2
                 have i₂ := b24e16 X0
                 grind)
              | exact superpose b24e16 b24e437253
              | exact resolve b24e437253 b24e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e437253
            have b24e762298 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (M.op X0 X2) X2) = (σ X1) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e762277 X0 X1 X2
                 have i₂ := b24e27 X0 X1
                 grind)
              | exact superpose b24e27 b24e762277
              | (have j0 := b24e762277 X0 X1 X2
                 grind)
              | exact resolve b24e762277 b24e27
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e27 b24e762277
            have b24e762350 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ X1) (τ (σ X0))) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
              intro X0 X1
              first
              | (have i₁ := b24e121428 X0 x
                 have i₂ := b24e762298 X0 X1 x
                 grind)
              | exact superpose b24e762298 b24e121428
              | (have j1 := b24e762298 X1 X0 x
                 grind)
              | exact resolve b24e121428 b24e762298
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e121428 b24e762298
            have b24e762362 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op (τ X1) X0) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b24e762350 X0 X1
                 have i₂ := b24e15 X0
                 grind)
              | exact superpose b24e15 b24e762350
              | (have j0 := b24e762350 X0 X1
                 grind)
              | exact resolve b24e762350 b24e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e762350
            have b24e763133 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (τ (σ X1)) X0) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b24e20 X1 X0
                 have i₂ := b24e762362 X0 (σ X1)
                 grind)
              | exact superpose b24e762362 b24e20
              | (have j1 := b24e762362 X0 (σ X1)
                 grind)
              | exact resolve b24e20 b24e762362
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e762362
            have b24e763137 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b24e763133 X0 X1
                 have i₂ := b24e15 X1
                 grind)
              | exact superpose b24e15 b24e763133
              | (have j0 := b24e763133 X0 X1
                 grind)
              | exact resolve b24e763133 b24e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e763133
            have b24e763226 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op y x) := by
              first
              | (have i₁ := b24e21
                 have i₂ := b24e763137 x y
                 grind)
              | exact superpose b24e763137 b24e21
              | (have j1 := b24e763137 x y
                 grind)
              | exact resolve b24e21 b24e763137
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e763137
            have b24e763253 : x = (M.op y x) := by
              first
              | (have j1 := b24e4723 y x
                 grind)
              | (have r₁ := b24e763226
                 have r₂ := b24e4723 y x
                 grind)
              | exact resolve b24e763226 b24e4723
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e4723 b24e763226
            have b24e763450 : ∀ X0 X1 : G, (M.op (M.op y x) X1) = (M.op (M.op y (M.op y X0)) X1) := by
              intro X0 X1
              first
              | (have i₁ := b24e704 y X0 X1 x
                 have i₂ := b24e763253
                 grind)
              | exact superpose b24e763253 b24e704
              | exact resolve b24e704 b24e763253
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e704
            have b24e763493 : ∀ X0 X1 : G, (M.op (M.op y (M.op y X0)) X1) = (M.op (M.op x x) X1) := by
              intro X0 X1
              first
              | (have i₁ := b24e2422 y X0 X1 x
                 have i₂ := b24e763253
                 grind)
              | exact superpose b24e763253 b24e2422
              | exact resolve b24e2422 b24e763253
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e2422
            have b24e763623 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op y X0)) X1) X1) = (σ (M.op (M.op x x) X0)) := by
              intro X0 X1
              first
              | (have i₁ := b24e27118 y x X0 X1
                 have i₂ := b24e763253
                 grind)
              | exact superpose b24e763253 b24e27118
              | exact resolve b24e27118 b24e763253
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e27118
            have b24e763730 : (σ (M.op y x)) = (M.op (σ y) (σ (M.op y x))) := by
              first
              | (have i₁ := b24e132002 y x
                 have i₂ := b24e763253
                 grind)
              | exact superpose b24e763253 b24e132002
              | exact resolve b24e132002 b24e763253
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e132002
            have b24e763794 : (σ x) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b24e763730
                 have i₂ := b24e763253
                 grind)
              | exact superpose b24e763253 b24e763730
              | exact resolve b24e763730 b24e763253
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e763730
            have b24e763978 : ∀ X1 : G, (M.op (M.op y x) X1) = (M.op (M.op x x) X1) := by
              intro X1
              first
              | (have i₁ := b24e763450 x X1
                 have i₂ := b24e763493 x X1
                 grind)
              | exact superpose b24e763493 b24e763450
              | exact resolve b24e763450 b24e763493
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e763450 b24e763493
            have b24e764281 : ∀ X1 : G, (M.op x X1) = (M.op (M.op x x) X1) := by
              intro X1
              first
              | (have i₁ := b24e763978 X1
                 have i₂ := b24e763253
                 grind)
              | exact superpose b24e763253 b24e763978
              | exact resolve b24e763978 b24e763253
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e763253 b24e763978
            have b24e785240 : ∀ X0 : G, (M.op (M.op (σ (M.op y y)) X0) X0) = (M.op (M.op (σ y) (σ x)) (σ y)) := by
              intro X0
              first
              | (have i₁ := b24e2706 y X0 (σ x)
                 have i₂ := b24e763794
                 grind)
              | exact superpose b24e763794 b24e2706
              | exact resolve b24e2706 b24e763794
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e2706
            have b24e785840 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op y y)) X0) X0) := by
              intro X0
              first
              | (have i₁ := b24e785240 X0
                 have i₂ := b24e763794
                 grind)
              | exact superpose b24e763794 b24e785240
              | exact resolve b24e785240 b24e763794
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e763794 b24e785240
            have b24e786123 : (M.op (σ x) (σ y)) = (σ (M.op (M.op x x) y)) := by
              first
              | (have i₁ := b24e785840 x
                 have i₂ := b24e763623 y x
                 grind)
              | exact superpose b24e763623 b24e785840
              | exact resolve b24e785840 b24e763623
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e763623 b24e785840
            have b24e786343 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b24e786123
                 have i₂ := b24e764281 y
                 grind)
              | exact superpose b24e764281 b24e786123
              | exact resolve b24e786123 b24e764281
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e764281 b24e786123
            have b24e786507 : False := by grind
            exact b24e786507
          · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
            · have b25e27 : (M.op x x) ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e29 : False := by grind
              exact b25e29
            · have b26e27 : (M.op x x) ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e29 : False := by grind
              exact b26e29

/-- `Equation4427`: `x ◇ (x ◇ y) = (z ◇ w) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_y_pyx_pyy_pxy_Equation4427 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law4427 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4427.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X0) := by
        intro X0 X1 X2 X3
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op x x) := by grind
      have b0e20 : (σ x) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e30 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op X0 X1) (σ x)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (σ x) (σ x) X0 X1
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 (σ x) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b0e34 X0 x
           have i₂ := b0e35 X0 x
           grind)
        | exact superpose b0e35 b0e34
        | exact resolve b0e34 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e38 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 X1) (σ x)) := by
        intro X0 X1
        first
        | (have i₁ := b0e30 X0 X1
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e30
        | exact resolve b0e30 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30
      have b0e43 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e37 (σ y)
           grind)
        | exact superpose b0e37 b0e18
        | exact resolve b0e18 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e46 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (σ x)) = (M.op x (M.op (σ x) X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 (σ x) X0 X1 X2
           have i₂ := b0e37 (M.op (σ x) X0)
           grind)
        | exact superpose b0e37 b0e11
        | exact resolve b0e11 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e47 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (σ x)) = (M.op x (M.op x X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e46 X0 X1 X2
           have i₂ := b0e37 X0
           grind)
        | exact superpose b0e37 b0e46
        | exact resolve b0e46 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37 b0e46
      have b0e50 : ∀ X1 X2 : G, (M.op x x) = (M.op (M.op X1 X2) (σ x)) := by
        intro X1 X2
        first
        | (have i₁ := b0e47 x X1 X2
           have i₂ := b0e35 x x
           grind)
        | exact superpose b0e35 b0e47
        | exact resolve b0e47 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47
      have b0e53 : (σ x) = (M.op x x) := by
        first
        | (have i₁ := b0e50 x x
           have i₂ := b0e38 x x
           grind)
        | exact superpose b0e38 b0e50
        | exact resolve b0e50 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38 b0e50
      have b0e56 : x = (σ x) := by
        first
        | (have i₁ := b0e53
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e53
        | exact resolve b0e53 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e53
      have b0e61 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op X0 x) := by
        intro X0
        first
        | (have i₁ := b0e14 x X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 x X0
           grind)
        | (have r₁ := b0e14 x x
           have r₂ := b0e19
           grind)
        | exact resolve b0e14 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e62 : ∀ X0 : G, (k x X0) = (M.op X0 x) := by
        intro X0
        first
        | (have j0 := b0e61 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61
      have b0e70 : ∀ X0 : G, (σ (k x X0)) = (k x (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 x X0
           have i₂ := b0e56
           grind)
        | exact superpose b0e56 b0e17
        | exact resolve b0e17 b0e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e71 : x = (τ x) := by
        first
        | (have i₁ := b0e12 x
           have i₂ := b0e56
           grind)
        | exact superpose b0e56 b0e12
        | exact resolve b0e12 b0e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e56
      have b0e72 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) x) := by
        intro X0
        first
        | (have i₁ := b0e70 X0
           have i₂ := b0e62 (σ X0)
           grind)
        | exact superpose b0e62 b0e70
        | exact resolve b0e70 b0e62
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e70
      have b0e73 : ∀ X0 : G, (M.op (σ X0) x) = (σ (M.op X0 x)) := by
        intro X0
        first
        | (have i₁ := b0e72 X0
           have i₂ := b0e62 X0
           grind)
        | exact superpose b0e62 b0e72
        | exact resolve b0e72 b0e62
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e62 b0e72
      have b0e81 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e14 X0 X1
           have i₂ := b0e16 X0 X2
           grind)
        | exact superpose b0e16 b0e14
        | (have j0 := b0e14 X0 X1
           have j1 := b0e16 X0 X2
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | (have r₁ := b0e14 X1 X1
           have r₂ := b0e16 X1 X1
           grind)
        | (have r₁ := b0e14 (M.op X0 X0) X1
           have r₂ := b0e16 X0 (M.op (M.op X0 X0) (M.op X0 X0))
           grind)
        | exact resolve b0e14 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e90 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e16 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e92 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
        intro X0 X1 X2
        first
        | (have j0 := b0e81 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e81
      have b0e120 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op X0 (M.op X0 X1))) = (M.op x (M.op X2 X3)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e35 (M.op X2 X3) X0
           have i₂ := b0e11 X0 X1 X2 X3
           grind)
        | exact superpose b0e11 b0e35
        | exact resolve b0e35 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e127 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X3) X0) = (M.op x X0) := by
        intro X0 X2 X3
        first
        | (have i₁ := b0e11 X0 x X2 X3
           have i₂ := b0e35 X0 x
           grind)
        | exact superpose b0e35 b0e11
        | exact resolve b0e11 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e135 : ∀ X0 X1 X2 X3 : G, (M.op x (M.op X2 X3)) = (M.op x (M.op X0 (M.op X0 X1))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e120 X0 X1 X2 X3
           have i₂ := b0e127 (M.op X0 (M.op X0 X1)) X2 X3
           grind)
        | exact superpose b0e127 b0e120
        | exact resolve b0e120 b0e127
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e120
      have b0e140 : ∀ X0 X2 X3 : G, (M.op x (M.op x X0)) = (M.op x (M.op X2 X3)) := by
        intro X0 X2 X3
        first
        | (have i₁ := b0e135 X0 x X2 X3
           have i₂ := b0e35 X0 x
           grind)
        | exact superpose b0e35 b0e135
        | exact resolve b0e135 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e135
      have b0e144 : ∀ X2 X3 : G, (M.op x x) = (M.op x (M.op X2 X3)) := by
        intro X2 X3
        first
        | (have i₁ := b0e140 x X2 X3
           have i₂ := b0e35 x x
           grind)
        | exact superpose b0e35 b0e140
        | exact resolve b0e140 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e140
      have b0e148 : ∀ X2 X3 : G, x = (M.op x (M.op X2 X3)) := by
        intro X2 X3
        first
        | (have i₁ := b0e144 X2 X3
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e144
        | exact resolve b0e144 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e144
      have b0e1269 : ∀ X0 X1 : G, (σ (k (M.op X0 x) X1)) = (k (M.op (σ X0) x) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 (M.op X0 x) X1
           have i₂ := b0e73 X0
           grind)
        | exact superpose b0e73 b0e17
        | exact resolve b0e17 b0e73
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e73
      have b0e1283 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e90 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e90
      have b0e1284 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e1283 X0
           have j1 := b0e14 X0 X0
           grind)
        | (have r₁ := b0e1283 X0
           have r₂ := b0e14 X0 x
           grind)
        | exact resolve b0e1283 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1283
      have b0e1287 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e1284 (σ X0)
           grind)
        | exact superpose b0e1284 b0e17
        | exact resolve b0e17 b0e1284
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1290 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e1287 X0
           have i₂ := b0e1284 X0
           grind)
        | exact superpose b0e1284 b0e1287
        | exact resolve b0e1287 b0e1284
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1284 b0e1287
      have b0e1574 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e92 X0 X1 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e92
      have b0e17973 : ∀ X0 X1 X2 : G, (M.op x X0) ≠ (M.op X0 (M.op X1 X2)) ∨ (M.op (M.op X1 X2) (M.op X1 X2)) = X0 ∨ (M.op x X0) = (k (M.op X1 X2) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e1574 (M.op X2 x) X0
           have i₂ := b0e127 X0 X2 x
           grind)
        | exact superpose b0e127 b0e1574
        | (have j0 := b0e1574 (M.op X1 X2) X0
           grind)
        | exact resolve b0e1574 b0e127
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1574
      have b0e18164 : ∀ X0 X1 X2 : G, (M.op x (M.op X1 X2)) = X0 ∨ (M.op x X0) ≠ (M.op X0 (M.op X1 X2)) ∨ (M.op x X0) = (k (M.op X1 X2) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e17973 X0 X1 X2
           have i₂ := b0e127 (M.op X1 X2) X1 X2
           grind)
        | exact superpose b0e127 b0e17973
        | (have j0 := b0e17973 X0 X1 X2
           grind)
        | (have r₁ := b0e17973 (M.op X2 x) X2 x
           have r₂ := b0e127 (M.op X2 x) X2 x
           grind)
        | exact resolve b0e17973 b0e127
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e127 b0e17973
      have b0e18235 : ∀ X0 X1 X2 : G, (M.op x X0) ≠ (M.op X0 (M.op X1 X2)) ∨ x = X0 ∨ (M.op x X0) = (k (M.op X1 X2) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e18164 X0 X1 X2
           have i₂ := b0e148 X1 X2
           grind)
        | exact superpose b0e148 b0e18164
        | (have j0 := b0e18164 X0 X1 X2
           grind)
        | exact resolve b0e18164 b0e148
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e148 b0e18164
      have b0e877240 : ∀ X0 X1 : G, (M.op x X0) ≠ (M.op x X0) ∨ x = X0 ∨ (M.op x X0) = (k (M.op X0 X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e18235 X0 X0 X1
           have i₂ := b0e35 X0 X1
           grind)
        | exact superpose b0e35 b0e18235
        | (have j0 := b0e18235 X0 X0 X1
           grind)
        | (have r₁ := b0e18235 X0 X0 X1
           have r₂ := b0e35 X0 X1
           grind)
        | exact resolve b0e18235 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35 b0e18235
      have b0e877243 : ∀ X0 X1 : G, (M.op x X0) = (k (M.op X0 X1) X0) ∨ x = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e877240 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e877240
      have b0e880402 : ∀ X0 : G, (M.op x (σ X0)) = (σ (k (M.op X0 x) X0)) ∨ (σ X0) = x := by
        intro X0
        first
        | (have i₁ := b0e1269 X0 X0
           have i₂ := b0e877243 (σ X0) x
           grind)
        | exact superpose b0e877243 b0e1269
        | (have j1 := b0e877243 (σ X0) x
           grind)
        | exact resolve b0e1269 b0e877243
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1269
      have b0e1017931 : ∀ X0 : G, (σ (M.op x X0)) = (M.op x (σ X0)) ∨ (σ X0) = x ∨ x = X0 := by
        intro X0
        first
        | (have i₁ := b0e880402 X0
           have i₂ := b0e877243 X0 x
           grind)
        | exact superpose b0e877243 b0e880402
        | (have j0 := b0e880402 X0
           have j1 := b0e877243 (σ X0) x
           grind)
        | exact resolve b0e880402 b0e877243
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e877243 b0e880402
      have b0e1512740 : (M.op x (σ y)) ≠ (M.op x (σ y)) ∨ x = (σ y) ∨ x = y := by
        first
        | (have i₁ := b0e43
           have i₂ := b0e1017931 y
           grind)
        | exact superpose b0e1017931 b0e43
        | (have j1 := b0e1017931 y
           grind)
        | (have r₁ := b0e43
           have r₂ := b0e1017931 y
           grind)
        | exact resolve b0e43 b0e1017931
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43 b0e1017931
      have b0e1512770 : x = (σ y) ∨ x = y := by grind
      clear b0e1512740
      have b0e1512773 : y = (τ x) ∨ x = y := by
        first
        | (have i₁ := b0e12 y
           have i₂ := b0e1512770
           grind)
        | exact superpose b0e1512770 b0e12
        | exact resolve b0e12 b0e1512770
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1512770
      have b0e1512864 : x = y ∨ x = y := by
        first
        | (have i₁ := b0e1512773
           have i₂ := b0e71
           grind)
        | exact superpose b0e71 b0e1512773
        | exact resolve b0e1512773 b0e71
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e71 b0e1512773
      have b0e1512865 : x = y := by grind
      clear b0e1512864
      have b0e1512885 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e1512865
           grind)
        | exact superpose b0e1512865 b0e18
        | exact resolve b0e18 b0e1512865
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1512865
      have b0e1512886 : False := by grind
      exact b0e1512886
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op x x) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e75 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b1e17 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1579 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e75 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e75
        have b1e1580 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e1579 X0
             have j1 := b1e15 X0 X0
             grind)
          | (have r₁ := b1e1579 X0
             have r₂ := b1e15 X0 x
             grind)
          | exact resolve b1e1579 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1579
        have b1e1583 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e1580 (σ X0)
             grind)
          | exact superpose b1e1580 b1e18
          | exact resolve b1e18 b1e1580
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1586 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e1583 X0
             have i₂ := b1e1580 X0
             grind)
          | exact superpose b1e1580 b1e1583
          | exact resolve b1e1583 b1e1580
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1580 b1e1583
        have b1e2870 : (σ y) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e1586 x
             grind)
          | exact superpose b1e1586 b1e22
          | exact resolve b1e22 b1e1586
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1586
        have b1e2916 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e2870
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e2870
          | exact resolve b1e2870 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2870
        have b1e2929 : False := by grind
        exact b1e2929
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op x x) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e67 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b2e17 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1116 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e67 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e67
        have b2e1117 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e1116 X0
             have j1 := b2e15 X0 X0
             grind)
          | (have r₁ := b2e1116 X0
             have r₂ := b2e15 X0 x
             grind)
          | exact resolve b2e1116 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1116
        have b2e1122 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e1117 (σ X0)
             grind)
          | exact superpose b2e1117 b2e18
          | exact resolve b2e18 b2e1117
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1129 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e1122 X0
             have i₂ := b2e1117 X0
             grind)
          | exact superpose b2e1117 b2e1122
          | exact resolve b2e1122 b2e1117
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1117 b2e1122
        have b2e1545 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e1129 x
             grind)
          | exact superpose b2e1129 b2e21
          | exact resolve b2e21 b2e1129
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1129
        have b2e1579 : (σ x) ≠ (σ x) := by
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
        have b2e1580 : False := by grind
        exact b2e1580
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : x ≠ (M.op x x) := by grind
        have b3e21 : y = (M.op x x) := by grind
        have b3e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e24 : x ≠ y := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e20
          | exact resolve b3e20 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e55 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e15 (σ x) X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e15
          | (have j0 := b3e15 (σ x) X0
             grind)
          | (have r₁ := b3e15 (σ x) x
             have r₂ := b3e22
             grind)
          | exact resolve b3e15 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e58 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have j0 := b3e55 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e55
        have b3e196 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e18 x X0
             have i₂ := b3e58 (σ X0)
             grind)
          | exact superpose b3e58 b3e18
          | exact resolve b3e18 b3e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e58
        have b3e790 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e196 x
             grind)
          | exact superpose b3e196 b3e22
          | exact resolve b3e22 b3e196
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e196
        have b3e1020 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e790
             have i₂ := b3e17 x x
             grind)
          | exact superpose b3e17 b3e790
          | (have j1 := b3e17 x x
             grind)
          | exact resolve b3e790 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e790
        have b3e1025 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
        clear b3e1020
        have b3e1030 : (σ x) = (σ y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e1025
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e1025
          | exact resolve b3e1025 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1025
        have b3e1031 : x = y ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e1030
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e1030
          | exact resolve b3e1030 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1030
        have b3e1032 : (σ x) = (σ y) := by
          first
          | (have r₁ := b3e1031
             have r₂ := b3e24
             grind)
          | exact resolve b3e1031 b3e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1031
        have b3e1478 : y = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 y
             have i₂ := b3e1032
             grind)
          | exact superpose b3e1032 b3e13
          | exact resolve b3e13 b3e1032
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1032
        have b3e1479 : x = y := by
          first
          | (have i₁ := b3e1478
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e1478
          | exact resolve b3e1478 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1478
        have b3e1484 : False := by grind
        exact b3e1484
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X0) := by
            intro X0 X1 X2 X3
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ (M.op x x) := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e23 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e26 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e23
            | exact resolve b4e23 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e27 : x ≠ y := by
            first
            | (have i₁ := b4e21
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e21
            | exact resolve b4e21 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e28 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b4e36 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 X1) (σ x)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (σ x) (σ x) X0 X1
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e37 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X4 X5) X2) := by
            intro X0 X1 X2 X4 X5
            first
            | (have i₁ := b4e13 X2 x X4 X5
               have i₂ := b4e13 X2 x X0 X1
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e40 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ y) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 X1 (σ x) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 X1 x x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e43 : ∀ X0 : G, (M.op (σ y) X0) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b4e40 X0 x
               have i₂ := b4e41 X0 x
               grind)
            | exact superpose b4e41 b4e40
            | exact resolve b4e40 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40
          have b4e48 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (σ y)) = (M.op y (M.op (σ y) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 (σ y) X0 X1 X2
               have i₂ := b4e43 (M.op (σ y) X0)
               grind)
            | exact superpose b4e43 b4e13
            | exact resolve b4e13 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e49 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (σ y)) = (M.op y (M.op y X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e48 X0 X1 X2
               have i₂ := b4e43 X0
               grind)
            | exact superpose b4e43 b4e48
            | exact resolve b4e48 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48
          have b4e52 : ∀ X1 X2 : G, (M.op (M.op X1 X2) (σ y)) = (M.op y y) := by
            intro X1 X2
            first
            | (have i₁ := b4e49 x X1 X2
               have i₂ := b4e41 y x
               grind)
            | exact superpose b4e41 b4e49
            | exact resolve b4e49 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49
          have b4e60 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op X0 (M.op X0 X1))) = (M.op y (M.op X2 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e41 (M.op X2 X3) X0
               have i₂ := b4e13 X0 X1 X2 X3
               grind)
            | exact superpose b4e13 b4e41
            | exact resolve b4e41 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e61 : (M.op (σ x) (σ y)) = (M.op y (σ x)) := by
            first
            | (have i₁ := b4e41 (σ x) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e41
            | exact resolve b4e41 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e63 : (M.op x y) = (M.op y x) := by
            first
            | (have i₁ := b4e41 x x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e41
            | exact resolve b4e41 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e66 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X3) X0) = (M.op y X0) := by
            intro X0 X2 X3
            first
            | (have i₁ := b4e13 X0 x X2 X3
               have i₂ := b4e41 X0 x
               grind)
            | exact superpose b4e41 b4e13
            | exact resolve b4e13 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e69 : ∀ X0 : G, (M.op y (M.op (σ y) X0)) = (M.op y (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e43 (M.op (σ y) X0)
               have i₂ := b4e41 (σ y) X0
               grind)
            | exact superpose b4e41 b4e43
            | exact resolve b4e43 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e70 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op y (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e69 X0
               have i₂ := b4e43 X0
               grind)
            | exact superpose b4e43 b4e69
            | exact resolve b4e69 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e69
          have b4e73 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op X2 X3)) = (M.op y (M.op X0 (M.op X0 X1))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e60 X0 X1 X2 X3
               have i₂ := b4e66 (M.op X0 (M.op X0 X1)) X2 X3
               grind)
            | exact superpose b4e66 b4e60
            | exact resolve b4e60 b4e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e60
          have b4e75 : (M.op y y) = (M.op y (σ y)) := by
            first
            | (have i₁ := b4e70 x
               have i₂ := b4e41 y x
               grind)
            | exact superpose b4e41 b4e70
            | exact resolve b4e70 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e70
          have b4e78 : ∀ X0 X2 X3 : G, (M.op y (M.op y X0)) = (M.op y (M.op X2 X3)) := by
            intro X0 X2 X3
            first
            | (have i₁ := b4e73 X0 x X2 X3
               have i₂ := b4e41 X0 x
               grind)
            | exact superpose b4e41 b4e73
            | exact resolve b4e73 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e73
          have b4e79 : ∀ X2 X3 : G, (M.op y y) = (M.op y (M.op X2 X3)) := by
            intro X2 X3
            first
            | (have i₁ := b4e78 x X2 X3
               have i₂ := b4e41 y x
               grind)
            | exact superpose b4e41 b4e78
            | exact resolve b4e78 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78
          have b4e90 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e16 X0 X1
               have i₂ := b4e18 X0 X2
               grind)
            | exact superpose b4e18 b4e16
            | (have j0 := b4e16 X0 X1
               have j1 := b4e18 X0 X2
               grind)
            | (have r₁ := b4e16 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e16 X1 X1
               have r₂ := b4e18 X1 X1
               grind)
            | (have r₁ := b4e16 (M.op X0 X0) X1
               have r₂ := b4e18 X0 (M.op (M.op X0 X0) (M.op X0 X0))
               grind)
            | exact resolve b4e16 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e94 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X2)) ∨ (M.op X3 X3) = X3 ∨ (M.op X3 X0) = (k X3 X0) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X1 X2 X3 X3
               have i₂ := b4e18 X3 X0
               grind)
            | (have i₁ := b4e13 X0 X1 X2 X3
               have i₂ := b4e18 X0 (M.op X2 X3)
               grind)
            | exact superpose b4e18 b4e13
            | (have j1 := b4e18 X3 X3
               grind)
            | exact resolve b4e13 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e101 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e18 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e102 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e18 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e103 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e90 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e90
          have b4e108 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op y X1) ∨ (M.op X3 X3) = X3 ∨ (M.op X3 X0) = (k X3 X0) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e94 X0 X1 x X3
               have i₂ := b4e41 X1 x
               grind)
            | exact superpose b4e41 b4e94
            | (have j0 := b4e94 X0 X1 x X3
               grind)
            | exact resolve b4e94 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41 b4e94
          have b4e133 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            grind
          have b4e135 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
          have b4e137 : (M.op y y) = (k x y) ∨ x = y := by grind
          have b4e153 : (M.op y y) = (k x y) := by
            first
            | (have r₁ := b4e137
               have r₂ := b4e27
               grind)
            | exact resolve b4e137 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e137
          have b4e155 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b4e135
               have r₂ := b4e26
               grind)
            | exact resolve b4e135 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26 b4e135
          have b4e156 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e133 X0 X1
               have j1 := b4e102 X1 X0
               grind)
            | (have r₁ := b4e133 X0 X1
               have r₂ := b4e102 (M.op X0 X0) (k X1 X0)
               grind)
            | (have r₁ := b4e133 X0 X1
               have r₂ := b4e102 (k X1 X0) (M.op X0 X0)
               grind)
            | (have r₁ := b4e133 X0 X1
               have r₂ := b4e102 X0 X1
               grind)
            | exact resolve b4e133 b4e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e102 b4e133
          have b4e162 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b4e155
               have i₂ := b4e19 x y
               grind)
            | exact superpose b4e19 b4e155
            | exact resolve b4e155 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e155
          have b4e167 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e162
               have i₂ := b4e153
               grind)
            | exact superpose b4e153 b4e162
            | exact resolve b4e162 b4e153
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e153 b4e162
          have b4e169 : (M.op y (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e167
               have i₂ := b4e43 (σ y)
               grind)
            | exact superpose b4e43 b4e167
            | exact resolve b4e167 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e167
          have b4e170 : (M.op y y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e169
               have i₂ := b4e75
               grind)
            | exact superpose b4e75 b4e169
            | exact resolve b4e169 b4e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e169
          have b4e175 : (M.op y y) = (τ (M.op y y)) := by
            first
            | (have i₁ := b4e14 (M.op y y)
               have i₂ := b4e170
               grind)
            | exact superpose b4e170 b4e14
            | exact resolve b4e14 b4e170
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e254 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X3) ≠ (M.op (M.op X0 X1) (M.op X2 X3)) ∨ (k (M.op X2 X3) X4) = (M.op X4 (M.op X2 X3)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e16 (M.op X2 X3) X4
               have i₂ := b4e37 X2 X3 (M.op X2 X3) X0 X1
               grind)
            | (have i₁ := b4e16 (M.op X2 X3) X4
               have i₂ := b4e37 X0 X1 (M.op X2 X3) X2 X3
               grind)
            | exact superpose b4e37 b4e16
            | (have j0 := b4e16 (M.op X2 X3) X4
               grind)
            | exact resolve b4e16 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37
          have b4e255 : ∀ X2 X3 X4 : G, (M.op X2 X3) ≠ (M.op y (M.op X2 X3)) ∨ (k (M.op X2 X3) X4) = (M.op X4 (M.op X2 X3)) := by
            intro X2 X3 X4
            first
            | (have i₁ := b4e254 x x X2 X3 X4
               have i₂ := b4e66 (M.op X2 X3) x x
               grind)
            | exact superpose b4e66 b4e254
            | (have j0 := b4e254 x x X2 X3 X4
               grind)
            | exact resolve b4e254 b4e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e66 b4e254
          have b4e291 : ∀ X2 X3 X4 : G, (M.op X2 X3) ≠ (M.op y y) ∨ (k (M.op X2 X3) X4) = (M.op X4 (M.op X2 X3)) := by
            intro X2 X3 X4
            first
            | (have i₁ := b4e255 X2 X3 X4
               have i₂ := b4e79 X2 X3
               grind)
            | exact superpose b4e79 b4e255
            | (have j0 := b4e255 X2 X3 X4
               grind)
            | (have r₁ := b4e255 y y X4
               have r₂ := b4e79 y y
               grind)
            | exact resolve b4e255 b4e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e79 b4e255
          have b4e1309 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e61
               grind)
            | exact superpose b4e61 b4e20
            | exact resolve b4e20 b4e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1327 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e101 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e101
          have b4e1328 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e1327 X0
               have j1 := b4e16 X0 X0
               grind)
            | (have r₁ := b4e1327 X0
               have r₂ := b4e16 X0 x
               grind)
            | exact resolve b4e1327 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1327
          have b4e1333 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e28 X0 (τ X0)
               have i₂ := b4e1328 (τ X0)
               grind)
            | exact superpose b4e1328 b4e28
            | exact resolve b4e28 b4e1328
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28
          have b4e1334 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e1333 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e1333
            | exact resolve b4e1333 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1333
          have b4e1339 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e1334 X0
               have i₂ := b4e1328 X0
               grind)
            | exact superpose b4e1328 b4e1334
            | exact resolve b4e1334 b4e1328
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1328 b4e1334
          have b4e1547 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e103 X0 X1 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e103
          have b4e1816 : ∀ X0 X1 : G, (σ y) = (M.op y (σ y)) ∨ (M.op X0 X1) = (M.op y X1) ∨ (M.op (σ y) X0) = (k (σ y) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e43 (σ y)
               have i₂ := b4e108 X0 X1 (σ y)
               grind)
            | exact superpose b4e108 b4e43
            | (have j1 := b4e108 X0 X1 (σ y)
               grind)
            | exact resolve b4e43 b4e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e108
          have b4e1832 : ∀ X0 X1 : G, (σ y) = (M.op y y) ∨ (M.op X0 X1) = (M.op y X1) ∨ (M.op (σ y) X0) = (k (σ y) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e1816 X0 X1
               have i₂ := b4e75
               grind)
            | exact superpose b4e75 b4e1816
            | (have j0 := b4e1816 X0 X1
               grind)
            | exact resolve b4e1816 b4e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1816
          have b4e1900 : ∀ X0 X1 : G, (M.op y X0) = (k (σ y) X0) ∨ (M.op X0 X1) = (M.op y X1) ∨ (σ y) = (M.op y y) := by
            intro X0 X1
            first
            | (have i₁ := b4e1832 X0 X1
               have i₂ := b4e43 X0
               grind)
            | exact superpose b4e43 b4e1832
            | (have j0 := b4e1832 X0 X1
               grind)
            | exact resolve b4e1832 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1832
          have b4e2413 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e156 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e156
          have b4e13512 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b4e1547 y x
               have i₂ := b4e63
               grind)
            | exact superpose b4e63 b4e1547
            | (have j0 := b4e1547 y x
               grind)
            | (have r₁ := b4e1547 x y
               have r₂ := b4e63
               grind)
            | (have r₁ := b4e1547 y x
               have r₂ := b4e63
               grind)
            | exact resolve b4e1547 b4e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e63 b4e1547
          have b4e13582 : (M.op x y) = (k y x) ∨ x = (M.op y y) := by grind
          clear b4e13512
          have b4e14765 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op y X0) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op y X0) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e2413 (σ y) X0
               have i₂ := b4e43 X0
               grind)
            | exact superpose b4e43 b4e2413
            | (have j0 := b4e2413 y X0
               grind)
            | (have r₁ := b4e2413 (σ y) y
               have r₂ := b4e43 y
               grind)
            | (have r₁ := b4e2413 y (σ y)
               have r₂ := b4e43 (σ y)
               grind)
            | exact resolve b4e2413 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2413
          have b4e14894 : ∀ X0 : G, (σ y) = (M.op y (σ y)) ∨ (M.op X0 X0) ≠ (M.op y X0) ∨ (M.op y X0) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e14765 X0
               have i₂ := b4e43 (σ y)
               grind)
            | exact superpose b4e43 b4e14765
            | (have j0 := b4e14765 X0
               grind)
            | (have r₁ := b4e14765 (σ y)
               have r₂ := b4e43 (σ y)
               grind)
            | exact resolve b4e14765 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43 b4e14765
          have b4e14945 : ∀ X0 : G, (σ y) = (M.op y y) ∨ (M.op X0 X0) ≠ (M.op y X0) ∨ (M.op y X0) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e14894 X0
               have i₂ := b4e75
               grind)
            | exact superpose b4e75 b4e14894
            | (have j0 := b4e14894 X0
               grind)
            | exact resolve b4e14894 b4e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e75 b4e14894
          have b4e14979 : ∀ X0 : G, (M.op y X0) = (k (σ y) X0) ∨ (σ y) = (M.op y y) := by
            intro X0
            first
            | (have j0 := b4e14945 X0
               have j1 := b4e1900 X0 x
               grind)
            | (have r₁ := b4e14945 x
               have r₂ := b4e1900 x x
               grind)
            | (have r₁ := b4e14945 y
               have r₂ := b4e1900 y y
               grind)
            | exact resolve b4e14945 b4e1900
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1900 b4e14945
          have b4e61312 : ∀ X0 : G, (M.op y (σ X0)) = (σ (k y X0)) ∨ (σ y) = (M.op y y) := by
            intro X0
            first
            | (have i₁ := b4e19 y X0
               have i₂ := b4e14979 (σ X0)
               grind)
            | exact superpose b4e14979 b4e19
            | exact resolve b4e19 b4e14979
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e14979
          have b4e173889 : (σ (M.op x y)) = (M.op y (σ x)) ∨ (σ y) = (M.op y y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b4e61312 x
               have i₂ := b4e13582
               grind)
            | exact superpose b4e13582 b4e61312
            | exact resolve b4e61312 b4e13582
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e61312
          have b4e174126 : (σ y) = (M.op y y) ∨ x = (M.op y y) := by
            first
            | (have r₁ := b4e173889
               have r₂ := b4e1309
               grind)
            | exact resolve b4e173889 b4e1309
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e173889
          have b4e175872 : (σ y) = (τ (σ y)) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b4e175
               have i₂ := b4e174126
               grind)
            | exact superpose b4e174126 b4e175
            | exact resolve b4e175 b4e174126
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e175971 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op y y) := by
            intro X0
            first
            | (have i₁ := b4e291 y y x
               have i₂ := b4e174126
               grind)
            | exact superpose b4e174126 b4e291
            | exact resolve b4e291 b4e174126
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e291 b4e174126
          have b4e176016 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ x = (M.op y y) := by
            intro X0
            first
            | (have j0 := b4e175971 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e175971
          have b4e176077 : x = (M.op y y) ∨ y = (σ y) := by
            first
            | (have i₁ := b4e175872
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e175872
            | exact resolve b4e175872 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e175872
          have b4e178805 : x = (τ x) ∨ y = (σ y) := by
            first
            | (have i₁ := b4e175
               have i₂ := b4e176077
               grind)
            | exact superpose b4e176077 b4e175
            | exact resolve b4e175 b4e176077
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e175 b4e176077
          have b4e180814 : (M.op x x) = (σ (M.op x x)) ∨ y = (σ y) := by
            first
            | (have i₁ := b4e1339 x
               have i₂ := b4e178805
               grind)
            | exact superpose b4e178805 b4e1339
            | exact resolve b4e1339 b4e178805
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1339 b4e178805
          have b4e180846 : y = (σ y) ∨ y = (σ y) := by
            first
            | (have i₁ := b4e180814
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e180814
            | exact resolve b4e180814 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e180814
          have b4e180847 : y = (σ y) := by grind
          clear b4e180846
          have b4e181413 : (M.op y (σ x)) = (M.op (σ x) y) := by
            first
            | (have i₁ := b4e61
               have i₂ := b4e180847
               grind)
            | exact superpose b4e180847 b4e61
            | exact resolve b4e61 b4e180847
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e61
          have b4e281555 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ x = (M.op y y) := by
            intro X0
            first
            | (have i₁ := b4e19 y X0
               have i₂ := b4e176016 (σ X0)
               grind)
            | exact superpose b4e176016 b4e19
            | exact resolve b4e19 b4e176016
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e176016
          have b4e281591 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) y) ∨ x = (M.op y y) := by
            intro X0
            first
            | (have i₁ := b4e281555 X0
               have i₂ := b4e180847
               grind)
            | exact superpose b4e180847 b4e281555
            | exact resolve b4e281555 b4e180847
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e281555
          have b4e290105 : (σ (M.op x y)) = (M.op (σ x) y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b4e281591 x
               have i₂ := b4e13582
               grind)
            | exact superpose b4e13582 b4e281591
            | exact resolve b4e281591 b4e13582
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13582 b4e281591
          have b4e290167 : (σ (M.op x y)) = (M.op (σ x) y) ∨ x = (M.op y y) := by grind
          clear b4e290105
          have b4e290183 : (σ (M.op x y)) = (M.op y (σ x)) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b4e290167
               have i₂ := b4e181413
               grind)
            | exact superpose b4e181413 b4e290167
            | exact resolve b4e290167 b4e181413
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e181413 b4e290167
          have b4e290190 : x = (M.op y y) := by
            first
            | (have r₁ := b4e290183
               have r₂ := b4e1309
               grind)
            | exact resolve b4e290183 b4e1309
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1309 b4e290183
          have b4e292304 : x = (σ x) := by
            first
            | (have i₁ := b4e170
               have i₂ := b4e290190
               grind)
            | exact superpose b4e290190 b4e170
            | exact resolve b4e170 b4e290190
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e170
          have b4e292416 : (M.op (σ x) (σ y)) = (M.op x (σ x)) := by
            first
            | (have i₁ := b4e36 y y
               have i₂ := b4e290190
               grind)
            | exact superpose b4e290190 b4e36
            | exact resolve b4e36 b4e290190
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e292424 : x = (M.op x (σ y)) := by
            first
            | (have i₁ := b4e52 y y
               have i₂ := b4e290190
               grind)
            | exact superpose b4e290190 b4e52
            | exact resolve b4e52 b4e290190
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e52 b4e290190
          have b4e292486 : x = (M.op x y) := by
            first
            | (have i₁ := b4e292424
               have i₂ := b4e180847
               grind)
            | exact superpose b4e180847 b4e292424
            | exact resolve b4e292424 b4e180847
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e292424
          have b4e292491 : (M.op x (σ x)) = (M.op (σ x) y) := by
            first
            | (have i₁ := b4e292416
               have i₂ := b4e180847
               grind)
            | exact superpose b4e180847 b4e292416
            | exact resolve b4e292416 b4e180847
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e180847 b4e292416
          have b4e292577 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b4e292491
               have i₂ := b4e292304
               grind)
            | exact superpose b4e292304 b4e292491
            | exact resolve b4e292491 b4e292304
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e292304 b4e292491
          have b4e292627 : y = (M.op x y) := by
            first
            | (have i₁ := b4e292577
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e292577
            | exact resolve b4e292577 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e292577
          have b4e292652 : x = y := by
            first
            | (have i₁ := b4e292627
               have i₂ := b4e292486
               grind)
            | exact superpose b4e292486 b4e292627
            | exact resolve b4e292627 b4e292486
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e292486 b4e292627
          have b4e292669 : False := by grind
          exact b4e292669
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op x x) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e73 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b5e18 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1078 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e73 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e73
          have b5e1079 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e1078 X0
               have j1 := b5e16 X0 X0
               grind)
            | (have r₁ := b5e1078 X0
               have r₂ := b5e16 X0 x
               grind)
            | exact resolve b5e1078 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1078
          have b5e1083 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e1079 (σ X0)
               grind)
            | exact superpose b5e1079 b5e19
            | exact resolve b5e19 b5e1079
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1088 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e1083 X0
               have i₂ := b5e1079 X0
               grind)
            | exact superpose b5e1079 b5e1083
            | exact resolve b5e1083 b5e1079
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1079 b5e1083
          have b5e1358 : (σ y) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e1088 x
               grind)
            | exact superpose b5e1088 b5e24
            | exact resolve b5e24 b5e1088
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1088
          have b5e1393 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e1358
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e1358
            | exact resolve b5e1358 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1358
          have b5e1394 : False := by grind
          exact b5e1394
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op x x) := by grind
        have b6e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e47 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e15 (σ x) X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e15
          | (have j0 := b6e15 (σ x) X0
             grind)
          | (have r₁ := b6e15 (σ x) x
             have r₂ := b6e22
             grind)
          | exact resolve b6e15 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e48 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have j0 := b6e47 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e47
        have b6e50 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e18 x X0
             have i₂ := b6e48 (σ X0)
             grind)
          | exact superpose b6e48 b6e18
          | exact resolve b6e18 b6e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e48
        have b6e446 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e50 x
             grind)
          | exact superpose b6e50 b6e22
          | exact resolve b6e22 b6e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e50
        have b6e617 : (k x x) = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e446
             grind)
          | exact superpose b6e446 b6e13
          | exact resolve b6e13 b6e446
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e446
        have b6e619 : x = (k x x) := by
          first
          | (have i₁ := b6e617
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e617
          | exact resolve b6e617 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e617
        have b6e627 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e619
             grind)
          | exact superpose b6e619 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e619
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e619
        have b6e628 : x = (M.op x x) := by grind
        clear b6e627
        have b6e630 : False := by grind
        exact b6e630
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op x x) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e81 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e18 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e872 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e81 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e81
          have b7e873 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e872 X0
               have j1 := b7e16 X0 X0
               grind)
            | (have r₁ := b7e872 X0
               have r₂ := b7e16 X0 x
               grind)
            | exact resolve b7e872 b7e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e872
          have b7e876 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e873 (σ X0)
               grind)
            | exact superpose b7e873 b7e19
            | exact resolve b7e19 b7e873
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e887 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e876 X0
               have i₂ := b7e873 X0
               grind)
            | exact superpose b7e873 b7e876
            | exact resolve b7e876 b7e873
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e873 b7e876
          have b7e906 : (σ y) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e887 x
               grind)
            | exact superpose b7e887 b7e24
            | exact resolve b7e24 b7e887
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e887
          have b7e1397 : (M.op x x) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op x x)
               have i₂ := b7e906
               grind)
            | exact superpose b7e906 b7e14
            | exact resolve b7e14 b7e906
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e906
          have b7e1398 : y = (M.op x x) := by
            first
            | (have i₁ := b7e1397
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e1397
            | exact resolve b7e1397 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1397
          have b7e1404 : False := by grind
          exact b7e1404
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op x x) := by grind
          have b8e22 : y ≠ (M.op x x) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e65 : ∀ X0 : G, (σ y) ≠ X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 (σ x) X0
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b8e18 b8e24
            | (have j1 := b8e18 (σ x) (σ x)
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e75 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
            intro X0
            first
            | (have j0 := b8e65 X0
               grind)
            | (have r₁ := b8e65 X0
               have r₂ := b8e23
               grind)
            | exact resolve b8e65 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e65
          have b8e265 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e75 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e75
          have b8e266 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e265
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e265
            | exact resolve b8e265 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e265
          have b8e294 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e266
               grind)
            | exact superpose b8e266 b8e20
            | exact resolve b8e20 b8e266
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e266
          have b8e332 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b8e294
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e294
            | (have j1 := b8e18 x x
               grind)
            | exact resolve b8e294 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e294
          have b8e333 : x = (M.op x x) ∨ y = (M.op x x) := by grind
          clear b8e332
          have b8e334 : y = (M.op x x) := by
            first
            | (have r₁ := b8e333
               have r₂ := b8e21
               grind)
            | exact resolve b8e333 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e333
          have b8e335 : False := by grind
          exact b8e335
