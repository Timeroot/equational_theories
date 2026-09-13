import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2162`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation2162 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2162 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2162.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e80 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
        intro X0
        grind
      have b0e81 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
        intro X0
        first
        | (have j0 := b0e80 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e80
      have b0e137 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b0e81 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e81
        | exact resolve b0e81 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e138 : (M.op x y) = (k y x) := by
        first
        | (have i₁ := b0e81 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e81
        | exact resolve b0e81 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e81
      have b0e141 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
        first
        | (have i₁ := b0e137
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e137
        | exact resolve b0e137 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e137
      have b0e142 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e141
           have i₂ := b0e138
           grind)
        | exact superpose b0e138 b0e141
        | exact resolve b0e141 b0e138
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e138 b0e141
      have b0e143 : False := by grind
      exact b0e143
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e39 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        have b1e40 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b1e39
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e39
          | exact resolve b1e39 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39
        have b1e77 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b1e78 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b1e77 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e77
        have b1e112 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e40
             grind)
          | exact superpose b1e40 b1e19
          | exact resolve b1e19 b1e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40
        have b1e161 : (M.op x y) = (k y x) := by
          first
          | (have i₁ := b1e78 x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e78
          | exact resolve b1e78 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e78
        have b1e167 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b1e112
             have i₂ := b1e161
             grind)
          | exact superpose b1e161 b1e112
          | exact resolve b1e112 b1e161
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e112 b1e161
        have b1e169 : False := by grind
        exact b1e169
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e51 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e70 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b2e71 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b2e70 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e70
        have b2e470 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e71 X0
             have i₂ := b2e51 X0 X1
             grind)
          | (have i₁ := b2e71 X0
             have i₂ := b2e51 X0 (M.op X0 X0)
             grind)
          | exact superpose b2e51 b2e71
          | (have j1 := b2e51 X1 X0
             grind)
          | exact resolve b2e71 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51 b2e71
        have b2e504 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e470 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e470
        have b2e4164 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e504 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e504
        have b2e4165 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e4164 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4164
        have b2e4196 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e4165 (σ X0)
             grind)
          | exact superpose b2e4165 b2e18
          | exact resolve b2e18 b2e4165
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e4203 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e4196 X0
             have i₂ := b2e4165 X0
             grind)
          | exact superpose b2e4165 b2e4196
          | exact resolve b2e4196 b2e4165
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4165 b2e4196
        have b2e4575 : (σ y) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e4203 x
             grind)
          | exact superpose b2e4203 b2e21
          | exact resolve b2e21 b2e4203
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4203
        have b2e4630 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e4575
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e4575
          | exact resolve b2e4575 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4575
        have b2e4631 : False := by grind
        exact b2e4631
  · rcases eq_or_ne (M.op y y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e21 : x = (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e38 : (M.op x y) = (k y x) := by grind
        have b3e66 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        have b3e80 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e66
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e66
          | exact resolve b3e66 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e66
        have b3e81 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e80
             have i₂ := b3e38
             grind)
          | exact superpose b3e38 b3e80
          | exact resolve b3e80 b3e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e80
        have b3e82 : (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have r₁ := b3e81
             have r₂ := b3e19
             grind)
          | exact resolve b3e81 b3e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e81
        have b3e92 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        clear b3e82
        have b3e93 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b3e92
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e92
          | exact resolve b3e92 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e92
        have b3e94 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e93
             have i₂ := b3e38
             grind)
          | exact superpose b3e38 b3e93
          | exact resolve b3e93 b3e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38 b3e93
        have b3e95 : False := by grind
        exact b3e95
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op y y) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e44 : (M.op x y) = (k y x) := by grind
          have b4e45 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
          have b4e47 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b4e45
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e45
            | exact resolve b4e45 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45
          have b4e48 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e47
               have i₂ := b4e44
               grind)
            | exact superpose b4e44 b4e47
            | exact resolve b4e47 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44 b4e47
          have b4e49 : False := by grind
          exact b4e49
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op y y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e58 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e78 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b5e79 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b5e78 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e78
          have b5e467 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e79 X0
               have i₂ := b5e58 X0 X1
               grind)
            | (have i₁ := b5e79 X0
               have i₂ := b5e58 X0 (M.op X0 X0)
               grind)
            | exact superpose b5e58 b5e79
            | (have j1 := b5e58 X1 X0
               grind)
            | exact resolve b5e79 b5e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58 b5e79
          have b5e499 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e467 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e467
          have b5e4139 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e499 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e499
          have b5e4140 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e4139 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4139
          have b5e4170 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e4140 (σ X0)
               grind)
            | exact superpose b5e4140 b5e19
            | exact resolve b5e19 b5e4140
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e4177 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e4170 X0
               have i₂ := b5e4140 X0
               grind)
            | exact superpose b5e4140 b5e4170
            | exact resolve b5e4170 b5e4140
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4140 b5e4170
          have b5e4560 : (σ x) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e4177 y
               grind)
            | exact superpose b5e4177 b5e24
            | exact resolve b5e24 b5e4177
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4177
          have b5e4614 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e4560
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e4560
            | exact resolve b5e4560 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4560
          have b5e4615 : False := by grind
          exact b5e4615
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e36 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
        have b6e38 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e36
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e36
          | exact resolve b6e36 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36
        have b6e61 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
        have b6e70 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e79 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b6e80 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b6e79 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e79
        have b6e82 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b6e70 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e70
        have b6e123 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e80 (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e80
          | exact resolve b6e80 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e129 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b6e123
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e123
          | exact resolve b6e123 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e123
        have b6e168 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e129
             grind)
          | exact superpose b6e129 b6e19
          | exact resolve b6e19 b6e129
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e129
        have b6e534 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ (M.op x y) = (k x y) := by
          first
          | (have i₁ := b6e168
             have i₂ := b6e61 x y
             grind)
          | exact superpose b6e61 b6e168
          | (have j1 := b6e61 x y
             grind)
          | exact resolve b6e168 b6e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e61 b6e168
        have b6e581 : y = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
        clear b6e534
        have b6e593 : (M.op x y) = (k x y) := by
          first
          | (have r₁ := b6e581
             have r₂ := b6e20
             grind)
          | exact resolve b6e581 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e581
        have b6e1759 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e64 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e64
          | exact resolve b6e64 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64
        have b6e2015 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e1759
        have b6e2094 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e2015
             grind)
          | exact superpose b6e2015 b6e13
          | exact resolve b6e13 b6e2015
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2015
        have b6e2108 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e2094
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e2094
          | exact resolve b6e2094 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2094
        have b6e2386 : y = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e82 x x
             have i₂ := b6e2108
             grind)
          | exact superpose b6e2108 b6e82
          | (have j0 := b6e82 x y
             grind)
          | exact resolve b6e82 b6e2108
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e82
        have b6e2387 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e2386
        have b6e2397 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e2387
             have r₂ := b6e20
             grind)
          | exact resolve b6e2387 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2387
        have b6e2684 : (M.op x x) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e80 x
             have i₂ := b6e2397
             grind)
          | exact superpose b6e2397 b6e80
          | exact resolve b6e80 b6e2397
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e80 b6e2397
        have b6e3416 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e2108
             have i₂ := b6e2684
             grind)
          | exact superpose b6e2684 b6e2108
          | exact resolve b6e2108 b6e2684
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2108 b6e2684
        have b6e3419 : y = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e3416
        have b6e3421 : (σ x) = (σ y) := by
          first
          | (have r₁ := b6e3419
             have r₂ := b6e20
             grind)
          | exact resolve b6e3419 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3419
        have b6e3965 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e3421
             grind)
          | exact superpose b6e3421 b6e19
          | exact resolve b6e19 b6e3421
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e3968 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e38
             have i₂ := b6e3421
             grind)
          | exact superpose b6e3421 b6e38
          | exact resolve b6e38 b6e3421
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38
        have b6e3980 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e3421
             grind)
          | exact superpose b6e3421 b6e13
          | exact resolve b6e13 b6e3421
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e3997 : x = y := by
          first
          | (have i₁ := b6e3980
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e3980
          | exact resolve b6e3980 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3980
        have b6e4004 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e3968
             have i₂ := b6e593
             grind)
          | exact superpose b6e593 b6e3968
          | exact resolve b6e3968 b6e593
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e593 b6e3968
        have b6e4005 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e3965
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e3965
          | exact resolve b6e3965 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3965
        have b6e4014 : (σ (M.op x y)) = (σ y) := by
          first
          | (have i₁ := b6e4004
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e4004
          | exact resolve b6e4004 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4004
        have b6e4015 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b6e4005
             have i₂ := b6e3421
             grind)
          | exact superpose b6e3421 b6e4005
          | exact resolve b6e4005 b6e3421
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4005
        have b6e4022 : (σ (M.op x y)) = (σ x) := by
          first
          | (have i₁ := b6e4014
             have i₂ := b6e3421
             grind)
          | exact superpose b6e3421 b6e4014
          | exact resolve b6e4014 b6e3421
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3421 b6e4014
        have b6e4023 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b6e4015
             have i₂ := b6e3997
             grind)
          | exact superpose b6e3997 b6e4015
          | exact resolve b6e4015 b6e3997
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4015
        have b6e4025 : (σ x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e4022
             have i₂ := b6e3997
             grind)
          | exact superpose b6e3997 b6e4022
          | exact resolve b6e4022 b6e3997
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3997 b6e4022
        have b6e4026 : False := by grind
        exact b6e4026
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : x ≠ (M.op y y) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e46 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
          have b7e48 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b7e46
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e46
            | exact resolve b7e46 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e49 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e48
               grind)
            | exact superpose b7e48 b7e20
            | exact resolve b7e20 b7e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
          have b7e74 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b7e49
               have i₂ := b7e18 y x
               grind)
            | exact superpose b7e18 b7e49
            | (have j1 := b7e18 y x
               grind)
            | exact resolve b7e49 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e75 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (M.op x x) := by
            first
            | (have r₁ := b7e74
               have r₂ := b7e22
               grind)
            | exact resolve b7e74 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e74
          have b7e76 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
            first
            | (have r₁ := b7e75
               have r₂ := b7e21
               grind)
            | exact resolve b7e75 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e75
          have b7e78 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e87 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b7e88 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b7e87 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e87
          have b7e90 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e78 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e78
          have b7e1916 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e71 y y
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e71
            | exact resolve b7e71 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e2183 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
          clear b7e1916
          have b7e2264 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e2183
               grind)
            | exact superpose b7e2183 b7e14
            | exact resolve b7e14 b7e2183
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2183
          have b7e2278 : x = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e2264
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e2264
            | exact resolve b7e2264 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2264
          have b7e2570 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e90 y y
               have i₂ := b7e2278
               grind)
            | exact superpose b7e2278 b7e90
            | (have j0 := b7e90 y x
               grind)
            | exact resolve b7e90 b7e2278
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90
          have b7e2571 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b7e2570
          have b7e2581 : y = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b7e2571
               have r₂ := b7e22
               grind)
            | exact resolve b7e2571 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2571
          have b7e2882 : (M.op y y) = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e88 y
               have i₂ := b7e2581
               grind)
            | exact superpose b7e2581 b7e88
            | exact resolve b7e88 b7e2581
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e88 b7e2581
          have b7e3662 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e2278
               have i₂ := b7e2882
               grind)
            | exact superpose b7e2882 b7e2278
            | exact resolve b7e2278 b7e2882
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2278 b7e2882
          have b7e3665 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b7e3662
          have b7e3667 : (σ x) = (σ y) := by
            first
            | (have r₁ := b7e3665
               have r₂ := b7e22
               grind)
            | exact resolve b7e3665 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3665
          have b7e4282 : y = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 y
               have i₂ := b7e3667
               grind)
            | exact superpose b7e3667 b7e14
            | exact resolve b7e14 b7e3667
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3667
          have b7e4295 : x = y := by
            first
            | (have i₁ := b7e4282
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e4282
            | exact resolve b7e4282 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4282
          have b7e4457 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e76
               have i₂ := b7e4295
               grind)
            | exact superpose b7e4295 b7e76
            | exact resolve b7e76 b7e4295
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e76 b7e4295
          have b7e4472 : False := by grind
          exact b7e4472
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b8e62 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (σ x) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
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
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ y) (σ x)
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e358 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e62 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62
          have b8e359 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e358
               have r₂ := b8e24
               grind)
            | exact resolve b8e358 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e358
          have b8e360 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e359
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e359
            | exact resolve b8e359 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e359
          have b8e361 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e360
               grind)
            | exact superpose b8e360 b8e20
            | exact resolve b8e20 b8e360
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e360
          have b8e379 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e361
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e361
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e361 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e361
          have b8e380 : y = (M.op x x) ∨ x = (M.op y y) := by grind
          clear b8e379
          have b8e381 : x = (M.op y y) := by
            first
            | (have r₁ := b8e380
               have r₂ := b8e21
               grind)
            | exact resolve b8e380 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e380
          have b8e383 : False := by grind
          exact b8e383

/-- `Equation2163`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_pyx_pyx_pxx_pyx_Equation2163 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2163 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2163.models_iff G M).mp hM
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
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
      have b0e46 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e52 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e46 (σ X0)
           grind)
        | exact superpose b0e46 b0e17
        | exact resolve b0e17 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e57 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e52 X0
           have i₂ := b0e46 X0
           grind)
        | exact superpose b0e46 b0e52
        | exact resolve b0e52 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46 b0e52
      have b0e237 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e57 x
           grind)
        | exact superpose b0e57 b0e22
        | (have r₁ := b0e22
           have r₂ := b0e57 x
           grind)
        | exact resolve b0e22 b0e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e57
      have b0e249 : False := by grind
      exact b0e249
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op x y) = (M.op x x) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e19
          | exact resolve b1e19 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e92 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e15 X0 X1
             have i₂ := b1e17 X0 X1
             grind)
          | (have i₁ := b1e15 X0 X0
             have i₂ := b1e17 X0 X1
             grind)
          | exact superpose b1e17 b1e15
          | (have j0 := b1e15 X0 X0
             have j1 := b1e17 X0 X1
             grind)
          | (have r₁ := b1e15 X0 X1
             have r₂ := b1e17 X0 X1
             grind)
          | (have r₁ := b1e15 X1 X1
             have r₂ := b1e17 X1 X1
             grind)
          | (have r₁ := b1e15 X0 X0
             have r₂ := b1e17 X0 X0
             grind)
          | exact resolve b1e15 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e102 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e16 X0 X1
             have i₂ := b1e17 X0 X1
             grind)
          | (have i₁ := b1e16 X0 X0
             have i₂ := b1e17 X0 X1
             grind)
          | exact superpose b1e17 b1e16
          | (have j0 := b1e16 X0 X1
             have j1 := b1e17 X0 X1
             grind)
          | (have r₁ := b1e16 X1 X1
             have r₂ := b1e17 X1 X1
             grind)
          | (have r₁ := b1e16 X0 X1
             have r₂ := b1e17 X0 X1
             grind)
          | (have r₁ := b1e16 X0 X0
             have r₂ := b1e17 X0 X0
             grind)
          | exact resolve b1e16 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e113 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e102 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e102
        have b1e114 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e113 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e113
        have b1e116 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e92 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e92
        have b1e117 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e116 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e116
        have b1e124 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e114 X0 X1
             have j1 := b1e15 X0 X1
             grind)
          | (have r₁ := b1e114 X0 X1
             have r₂ := b1e15 X0 X1
             grind)
          | (have r₁ := b1e114 X1 X1
             have r₂ := b1e15 X1 X1
             grind)
          | exact resolve b1e114 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e114
        have b1e460 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e124 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e124
        have b1e467 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e460 X0 X1
             have j1 := b1e117 X0 X1
             grind)
          | (have r₁ := b1e460 X0 X1
             have r₂ := b1e117 X0 X1
             grind)
          | (have r₁ := b1e460 X0 X0
             have r₂ := b1e117 X0 X0
             grind)
          | exact resolve b1e460 b1e117
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e117 b1e460
        have b1e509 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X1 X0
             have i₂ := b1e467 (σ X1) (σ X0)
             grind)
          | exact superpose b1e467 b1e18
          | exact resolve b1e18 b1e467
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e517 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e509 X0 X1
             have i₂ := b1e467 X1 X0
             grind)
          | exact superpose b1e467 b1e509
          | exact resolve b1e509 b1e467
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e467 b1e509
        have b1e1037 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e517 x y
             grind)
          | exact superpose b1e517 b1e23
          | exact resolve b1e23 b1e517
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23 b1e517
        have b1e1078 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e1037
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1037
          | exact resolve b1e1037 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1037
        have b1e1079 : False := by grind
        exact b1e1079
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b2e84 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b2e94 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
          | (have r₁ := b2e16 X1 X1
             have r₂ := b2e17 X1 X1
             grind)
          | (have r₁ := b2e16 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e16 X0 X0
             have r₂ := b2e17 X0 X0
             grind)
          | exact resolve b2e16 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e105 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e94 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e94
        have b2e106 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e105 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e105
        have b2e108 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e84 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e84
        have b2e109 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e108 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e108
        have b2e116 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e106 X0 X1
             have j1 := b2e15 X0 X1
             grind)
          | (have r₁ := b2e106 X0 X1
             have r₂ := b2e15 X0 X1
             grind)
          | (have r₁ := b2e106 X1 X1
             have r₂ := b2e15 X1 X1
             grind)
          | exact resolve b2e106 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e106
        have b2e484 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e116 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e116
        have b2e491 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e484 X0 X1
             have j1 := b2e109 X0 X1
             grind)
          | (have r₁ := b2e484 X0 X1
             have r₂ := b2e109 X0 X1
             grind)
          | (have r₁ := b2e484 X0 X0
             have r₂ := b2e109 X0 X0
             grind)
          | exact resolve b2e484 b2e109
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e109 b2e484
        have b2e532 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e491 (σ X1) (σ X0)
             grind)
          | exact superpose b2e491 b2e18
          | exact resolve b2e18 b2e491
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e539 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e532 X0 X1
             have i₂ := b2e491 X1 X0
             grind)
          | exact superpose b2e491 b2e532
          | exact resolve b2e532 b2e491
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e491 b2e532
        have b2e878 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e23
             have i₂ := b2e539 x y
             grind)
          | exact superpose b2e539 b2e23
          | exact resolve b2e23 b2e539
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23 b2e539
        have b2e915 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e878
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e878
          | exact resolve b2e878 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e878
        have b2e916 : False := by grind
        exact b2e916
  · rcases eq_or_ne (M.op x x) (M.op y x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b3e53 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
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
        have b3e54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e55 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
        clear b3e53
        have b3e56 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
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
        have b3e58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 X0
             have i₂ := b3e54 (σ X0)
             grind)
          | exact superpose b3e54 b3e18
          | exact resolve b3e18 b3e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e58 X0
             have i₂ := b3e54 X0
             grind)
          | exact superpose b3e54 b3e58
          | exact resolve b3e58 b3e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54 b3e58
        have b3e71 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
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
        have b3e74 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by grind
        clear b3e71
        have b3e75 : (M.op x x) = (k x y) := by
          first
          | (have r₁ := b3e74
             have r₂ := b3e20
             grind)
          | exact resolve b3e74 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e74
        have b3e92 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b3e103 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
          | (have r₁ := b3e16 X1 X1
             have r₂ := b3e17 X1 X1
             grind)
          | (have r₁ := b3e16 X0 X1
             have r₂ := b3e17 X0 X1
             grind)
          | (have r₁ := b3e16 X0 X0
             have r₂ := b3e17 X0 X0
             grind)
          | exact resolve b3e16 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e114 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e17 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e116 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e103 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e103
        have b3e117 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e116 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e116
        have b3e119 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e92 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e92
        have b3e120 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e119 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e119
        have b3e123 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e114 X0 X1
             have j1 := b3e15 X0 X1
             grind)
          | (have r₁ := b3e114 X0 X1
             have r₂ := b3e15 X0 X1
             grind)
          | (have r₁ := b3e114 X1 X1
             have r₂ := b3e15 X1 X1
             grind)
          | exact resolve b3e114 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e114
        have b3e128 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e117 X0 X1
             have j1 := b3e15 X0 X1
             grind)
          | (have r₁ := b3e117 X0 X1
             have r₂ := b3e15 X0 X1
             grind)
          | (have r₁ := b3e117 X1 X1
             have r₂ := b3e15 X1 X1
             grind)
          | exact resolve b3e117 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e117
        have b3e229 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e65 x
             grind)
          | exact superpose b3e65 b3e23
          | exact resolve b3e23 b3e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23
        have b3e404 : (M.op (σ x) (σ y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b3e123 (σ y) (σ x)
             have i₂ := b3e56
             grind)
          | exact superpose b3e56 b3e123
          | (have j0 := b3e123 (σ y) (σ x)
             grind)
          | exact resolve b3e123 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e56 b3e123
        have b3e434 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b3e404
             have i₂ := b3e75
             grind)
          | exact superpose b3e75 b3e404
          | exact resolve b3e404 b3e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e75 b3e404
        have b3e440 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b3e434
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e434
          | exact resolve b3e434 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e434
        have b3e443 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have r₁ := b3e440
             have r₂ := b3e65 x
             grind)
          | exact resolve b3e440 b3e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e440
        have b3e444 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b3e443
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e443
          | exact resolve b3e443 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e443
        have b3e446 : (M.op (σ x) (σ x)) = (σ (k y x)) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e444
             grind)
          | exact superpose b3e444 b3e22
          | exact resolve b3e22 b3e444
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e444
        have b3e456 : (σ (M.op x x)) = (σ (k y x)) := by
          first
          | (have i₁ := b3e446
             have i₂ := b3e65 x
             grind)
          | exact superpose b3e65 b3e446
          | exact resolve b3e446 b3e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e65 b3e446
        have b3e504 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e128 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e128
        have b3e511 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e504 X0 X1
             have j1 := b3e120 X0 X1
             grind)
          | (have r₁ := b3e504 X0 X1
             have r₂ := b3e120 X0 X1
             grind)
          | (have r₁ := b3e504 X0 X0
             have r₂ := b3e120 X0 X0
             grind)
          | exact resolve b3e504 b3e120
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e120 b3e504
        have b3e612 : (σ (M.op x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e456
             have i₂ := b3e511 y x
             grind)
          | exact superpose b3e511 b3e456
          | exact resolve b3e456 b3e511
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e456 b3e511
        have b3e630 : False := by grind
        exact b3e630
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e110 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
          have b4e120 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e17 X0 X0
               have r₂ := b4e18 X0 X0
               grind)
            | exact resolve b4e17 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e134 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e120 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e120
          have b4e135 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e134 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e134
          have b4e137 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e110 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e110
          have b4e138 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e137 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e137
          have b4e147 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e135 X0 X1
               have j1 := b4e16 X0 X1
               grind)
            | (have r₁ := b4e135 X0 X1
               have r₂ := b4e16 X0 X1
               grind)
            | (have r₁ := b4e135 X1 X1
               have r₂ := b4e16 X1 X1
               grind)
            | exact resolve b4e135 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e135
          have b4e483 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e147 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e147
          have b4e490 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e483 X0 X1
               have j1 := b4e138 X0 X1
               grind)
            | (have r₁ := b4e483 X0 X1
               have r₂ := b4e138 X0 X1
               grind)
            | (have r₁ := b4e483 X0 X0
               have r₂ := b4e138 X0 X0
               grind)
            | exact resolve b4e483 b4e138
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e138 b4e483
          have b4e532 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 X0
               have i₂ := b4e490 (σ X1) (σ X0)
               grind)
            | exact superpose b4e490 b4e19
            | exact resolve b4e19 b4e490
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e540 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e532 X0 X1
               have i₂ := b4e490 X1 X0
               grind)
            | exact superpose b4e490 b4e532
            | exact resolve b4e532 b4e490
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e490 b4e532
          have b4e814 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e540 x y
               grind)
            | exact superpose b4e540 b4e20
            | (have r₁ := b4e20
               have r₂ := b4e540 x y
               grind)
            | exact resolve b4e20 b4e540
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e540
          have b4e841 : False := by grind
          exact b4e841
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e103 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
          have b5e113 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
            | (have r₁ := b5e17 X1 X1
               have r₂ := b5e18 X1 X1
               grind)
            | (have r₁ := b5e17 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | (have r₁ := b5e17 X0 X0
               have r₂ := b5e18 X0 X0
               grind)
            | exact resolve b5e17 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e127 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e113 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e113
          have b5e128 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e127 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e127
          have b5e130 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e103 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e103
          have b5e131 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e130 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e130
          have b5e140 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e128 X0 X1
               have j1 := b5e16 X0 X1
               grind)
            | (have r₁ := b5e128 X0 X1
               have r₂ := b5e16 X0 X1
               grind)
            | (have r₁ := b5e128 X1 X1
               have r₂ := b5e16 X1 X1
               grind)
            | exact resolve b5e128 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e128
          have b5e468 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e140 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e140
          have b5e475 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e468 X0 X1
               have j1 := b5e131 X0 X1
               grind)
            | (have r₁ := b5e468 X0 X1
               have r₂ := b5e131 X0 X1
               grind)
            | (have r₁ := b5e468 X0 X0
               have r₂ := b5e131 X0 X0
               grind)
            | exact resolve b5e468 b5e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e131 b5e468
          have b5e517 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X1 X0
               have i₂ := b5e475 (σ X1) (σ X0)
               grind)
            | exact superpose b5e475 b5e19
            | exact resolve b5e19 b5e475
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e525 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e517 X0 X1
               have i₂ := b5e475 X1 X0
               grind)
            | exact superpose b5e475 b5e517
            | exact resolve b5e517 b5e475
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e475 b5e517
          have b5e847 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e525 x y
               grind)
            | exact superpose b5e525 b5e20
            | (have r₁ := b5e20
               have r₂ := b5e525 x y
               grind)
            | exact resolve b5e20 b5e525
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e525
          have b5e874 : False := by grind
          exact b5e874
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b6e89 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b6e100 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
          | (have r₁ := b6e16 X1 X1
             have r₂ := b6e17 X1 X1
             grind)
          | (have r₁ := b6e16 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e16 X0 X0
             have r₂ := b6e17 X0 X0
             grind)
          | exact resolve b6e16 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e111 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e100 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e100
        have b6e112 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e111 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e111
        have b6e114 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e89 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e89
        have b6e115 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e114 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e114
        have b6e122 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e112 X0 X1
             have j1 := b6e15 X0 X1
             grind)
          | (have r₁ := b6e112 X0 X1
             have r₂ := b6e15 X0 X1
             grind)
          | (have r₁ := b6e112 X1 X1
             have r₂ := b6e15 X1 X1
             grind)
          | exact resolve b6e112 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e112
        have b6e486 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e122 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e122
        have b6e493 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e486 X0 X1
             have j1 := b6e115 X0 X1
             grind)
          | (have r₁ := b6e486 X0 X1
             have r₂ := b6e115 X0 X1
             grind)
          | (have r₁ := b6e486 X0 X0
             have r₂ := b6e115 X0 X0
             grind)
          | exact resolve b6e486 b6e115
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e115 b6e486
        have b6e538 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e29 X1 X0
             have i₂ := b6e493 X1 (σ X0)
             grind)
          | exact superpose b6e493 b6e29
          | exact resolve b6e29 b6e493
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e29
        have b6e541 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e538 X0 X1
             have i₂ := b6e493 (τ X1) X0
             grind)
          | exact superpose b6e493 b6e538
          | exact resolve b6e538 b6e493
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e493 b6e538
        have b6e680 : (M.op x (τ (σ y))) = (τ (M.op (σ x) (σ x))) := by
          first
          | (have i₁ := b6e541 x (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e541
          | exact resolve b6e541 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e707 : (M.op x (τ (σ y))) = (M.op x (τ (σ x))) := by
          first
          | (have i₁ := b6e680
             have i₂ := b6e541 x (σ x)
             grind)
          | exact superpose b6e541 b6e680
          | exact resolve b6e680 b6e541
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e541 b6e680
        have b6e717 : (M.op x x) = (M.op x (τ (σ y))) := by
          first
          | (have i₁ := b6e707
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e707
          | exact resolve b6e707 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e707
        have b6e720 : (M.op x y) = (M.op x x) := by
          first
          | (have i₁ := b6e717
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e717
          | exact resolve b6e717 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e717
        have b6e721 : False := by grind
        exact b6e721
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
          have b7e84 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
          have b7e86 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e84
          have b7e87 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e86
               have r₂ := b7e23
               grind)
            | exact resolve b7e86 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e86
          have b7e88 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
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
          have b7e89 : (σ (k x y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e88
               have i₂ := b7e75 x
               grind)
            | exact superpose b7e75 b7e88
            | exact resolve b7e88 b7e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e75 b7e88
          have b7e94 : (k x y) = (τ (σ (M.op x x))) := by
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
          have b7e95 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b7e94
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e94
            | exact resolve b7e94 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e94
          have b7e167 : (M.op x x) = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y x) := by
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
          have b7e168 : (M.op x x) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by grind
          clear b7e167
          have b7e170 : (M.op x y) = (M.op x x) := by
            first
            | (have r₁ := b7e168
               have r₂ := b7e22
               grind)
            | exact resolve b7e168 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e168
          have b7e172 : False := by grind
          exact b7e172
        · have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e110 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
          have b8e121 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
            | (have r₁ := b8e17 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e17 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | exact resolve b8e17 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e133 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e121 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e121
          have b8e134 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e133 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e133
          have b8e136 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e110 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e110
          have b8e137 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e136 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e136
          have b8e145 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
          have b8e478 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e145 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e145
          have b8e485 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e478 X0 X1
               have j1 := b8e137 X0 X1
               grind)
            | (have r₁ := b8e478 X0 X1
               have r₂ := b8e137 X0 X1
               grind)
            | (have r₁ := b8e478 X0 X0
               have r₂ := b8e137 X0 X0
               grind)
            | exact resolve b8e478 b8e137
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e137 b8e478
          have b8e521 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e485 (σ X1) (σ X0)
               grind)
            | exact superpose b8e485 b8e19
            | exact resolve b8e19 b8e485
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e532 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e521 X0 X1
               have i₂ := b8e485 X1 X0
               grind)
            | exact superpose b8e485 b8e521
            | exact resolve b8e521 b8e485
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e485 b8e521
          have b8e1048 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e532 x y
               grind)
            | exact superpose b8e532 b8e20
            | (have r₁ := b8e20
               have r₂ := b8e532 x y
               grind)
            | exact resolve b8e20 b8e532
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e532
          have b8e1085 : False := by grind
          exact b8e1085

/-- `Equation2163`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pxx_x_pxy_Equation2163 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2163 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2163.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (M.op x y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op x y) = (M.op x x) := by grind
      have b0e20 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e18
        | exact resolve b0e18 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e23 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
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
      have b0e45 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
        first
        | (have i₁ := b0e14 x y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 x x
           grind)
        | (have r₁ := b0e14 x y
           have r₂ := b0e19
           grind)
        | exact resolve b0e14 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e46 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
        first
        | (have i₁ := b0e14 (σ x) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have j0 := b0e14 (σ x) (σ x)
           grind)
        | (have r₁ := b0e14 (σ x) (σ y)
           have r₂ := b0e20
           grind)
        | exact resolve b0e14 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e48 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
      clear b0e46
      have b0e49 : (M.op x x) = (k x y) := by grind
      clear b0e45
      have b0e50 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e48
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e48
        | exact resolve b0e48 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48
      have b0e51 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b0e50
           have i₂ := b0e49
           grind)
        | exact superpose b0e49 b0e50
        | exact resolve b0e50 b0e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e49 b0e50
      have b0e52 : False := by grind
      exact b0e52
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
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
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op x y) = (M.op x x) := by grind
        have b2e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e19
          | exact resolve b2e19 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e52 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
          first
          | (have i₁ := b2e15 x y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e15
          | (have j0 := b2e15 x x
             grind)
          | (have r₁ := b2e15 x y
             have r₂ := b2e20
             grind)
          | exact resolve b2e15 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e54 : (M.op x x) = (k x y) := by grind
        clear b2e52
        have b2e56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e53 (σ X0)
             grind)
          | exact superpose b2e53 b2e18
          | exact resolve b2e18 b2e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e63 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e56 X0
             have i₂ := b2e53 X0
             grind)
          | exact superpose b2e53 b2e56
          | exact resolve b2e56 b2e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53 b2e56
        have b2e71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
        have b2e87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e71 X0 X1
             have i₂ := b2e63 X0
             grind)
          | exact superpose b2e63 b2e71
          | (have j0 := b2e71 X0 X1
             grind)
          | exact resolve b2e71 b2e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e71
        have b2e805 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e87 x y
             grind)
          | exact superpose b2e87 b2e21
          | (have j1 := b2e87 x y
             grind)
          | exact resolve b2e21 b2e87
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e87
        have b2e875 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b2e805
             have r₂ := b2e24
             grind)
          | exact resolve b2e805 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e805
        have b2e888 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e875
             have r₂ := b2e22
             grind)
          | exact resolve b2e875 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e875
        have b2e894 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e888
             have i₂ := b2e54
             grind)
          | exact superpose b2e54 b2e888
          | exact resolve b2e888 b2e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e54 b2e888
        have b2e896 : False := by grind
        exact b2e896
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b3e21 : x = y := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e27 : False := by grind
        exact b3e27
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e22 : x = y := by grind
          have b4e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e30 : False := by grind
          exact b4e30
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e21 : x ≠ y := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e24 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e19
          | exact resolve b6e19 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e52 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e15
          | (have j0 := b6e15 (σ x) (σ x)
             grind)
          | (have r₁ := b6e15 (σ x) (σ y)
             have r₂ := b6e22
             grind)
          | exact resolve b6e15 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e54 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b6e52
        have b6e55 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e54
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e54
          | exact resolve b6e54 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e54
        have b6e92 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e24
             have i₂ := b6e55
             grind)
          | exact superpose b6e55 b6e24
          | exact resolve b6e24 b6e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24 b6e55
        have b6e125 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b6e92
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e92
          | (have j1 := b6e17 x y
             grind)
          | (have r₁ := b6e92
             have r₂ := b6e17 (σ (M.op x y)) (σ (k x y))
             grind)
          | (have r₁ := b6e92
             have r₂ := b6e17 (σ (k x y)) (σ (M.op x y))
             grind)
          | exact resolve b6e92 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e92
        have b6e126 : (M.op x y) = (M.op x x) ∨ x = y := by grind
        clear b6e125
        have b6e127 : x = y := by
          first
          | (have r₁ := b6e126
             have r₂ := b6e20
             grind)
          | exact resolve b6e126 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e126
        have b6e128 : False := by grind
        exact b6e128
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b7e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ x) = (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
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
          have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : x ≠ y := by grind
          have b8e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
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
          have b8e43 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e45 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e43 (σ X0)
               grind)
            | exact superpose b8e43 b8e19
            | exact resolve b8e19 b8e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e50 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e45 X0
               have i₂ := b8e43 X0
               grind)
            | exact superpose b8e43 b8e45
            | exact resolve b8e45 b8e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43 b8e45
          have b8e56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e64 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
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
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 (M.op X0 X0) (M.op X0 X1)
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e68 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e64 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e64
          have b8e71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e56 X0 X1
               have i₂ := b8e50 X0
               grind)
            | exact superpose b8e50 b8e56
            | (have j0 := b8e56 X0 X1
               grind)
            | exact resolve b8e56 b8e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e56
          have b8e174 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e68 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e68
          have b8e177 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e174 X0 X1
               have j1 := b8e18 X0 X1
               grind)
            | (have r₁ := b8e174 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e174 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | (have r₁ := b8e174 X0 X1
               have r₂ := b8e18 (M.op X0 X0) (M.op X0 X1)
               grind)
            | exact resolve b8e174 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e174
          have b8e245 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X0 X1
               have i₂ := b8e177 (τ X0) X1
               grind)
            | exact superpose b8e177 b8e26
            | (have j1 := b8e177 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
               grind)
            | exact resolve b8e26 b8e177
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e177
          have b8e671 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
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
          have b8e740 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e671
               have r₂ := b8e24
               grind)
            | exact resolve b8e671 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e671
          have b8e1327 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e245 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e245
            | exact resolve b8e245 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e245
          have b8e1361 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e1327 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e1327
            | (have j0 := b8e1327 (σ (k X0 X1)) (σ (M.op X0 X1))
               grind)
            | exact resolve b8e1327 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1327
          have b8e2763 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = y := by
            first
            | (have i₁ := b8e740
               have i₂ := b8e1361 x y
               grind)
            | exact superpose b8e1361 b8e740
            | (have j1 := b8e1361 (M.op (σ x) (σ y)) (σ (M.op x x))
               grind)
            | (have r₁ := b8e740
               have r₂ := b8e1361 x y
               grind)
            | (have r₁ := b8e740
               have r₂ := b8e1361 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e740
               have r₂ := b8e1361 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e740 b8e1361
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e740 b8e1361
          have b8e2764 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = y := by grind
          clear b8e2763
          have b8e2770 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e2764
               have r₂ := b8e22
               grind)
            | exact resolve b8e2764 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2764
          have b8e2777 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e2770
               grind)
            | exact superpose b8e2770 b8e23
            | exact resolve b8e23 b8e2770
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2770
          have b8e2819 : False := by grind
          exact b8e2819

/-- `Equation2291`: `x = (y ◇ (x ◇ (x ◇ x))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(X,X) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pyx_pxx_pyy_pyx_Equation2291 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2291 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2291.models_iff G M).mp hM
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
    · have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
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
      have b0e27 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e12 (k (τ X0) X1)
           have i₂ := b0e21 X0 X1
           grind)
        | exact superpose b0e21 b0e12
        | exact resolve b0e12 b0e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e33 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e12 (k X0 (τ X1))
           have i₂ := b0e22 X1 X0
           grind)
        | exact superpose b0e22 b0e12
        | exact resolve b0e12 b0e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e38 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e44 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e38 (σ X0)
           grind)
        | exact superpose b0e38 b0e17
        | exact resolve b0e17 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e46 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
        intro X0
        first
        | (have i₁ := b0e22 X0 (τ X0)
           have i₂ := b0e38 (τ X0)
           grind)
        | exact superpose b0e38 b0e22
        | exact resolve b0e22 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e47 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e46 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e46
        | exact resolve b0e46 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46
      have b0e49 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e44 X0
           have i₂ := b0e38 X0
           grind)
        | exact superpose b0e38 b0e44
        | exact resolve b0e44 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44
      have b0e51 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e47 X0
           have i₂ := b0e38 X0
           grind)
        | exact superpose b0e38 b0e47
        | exact resolve b0e47 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38 b0e47
      have b0e74 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 X0 X0
           have i₂ := b0e16 X0 X1
           grind)
        | (have i₁ := b0e15 X0 X1
           have i₂ := b0e16 X0 X1
           grind)
        | exact superpose b0e16 b0e15
        | (have j0 := b0e15 X0 X1
           have j1 := b0e16 X0 X1
           grind)
        | (have r₁ := b0e15 X0 X0
           have r₂ := b0e16 X0 X0
           grind)
        | (have r₁ := b0e15 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | exact resolve b0e15 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e76 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e22 X0 X1
           have i₂ := b0e16 X1 (τ X0)
           grind)
        | exact superpose b0e16 b0e22
        | (have j1 := b0e16 X1 (τ X0)
           grind)
        | exact resolve b0e22 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e77 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X1 X0
           have i₂ := b0e16 (σ X1) (σ X0)
           grind)
        | exact superpose b0e16 b0e17
        | (have j1 := b0e16 (σ X1) (σ X0)
           grind)
        | exact resolve b0e17 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e81 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e16 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e83 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e74 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e74
      have b0e88 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e77 X0 X1
           have i₂ := b0e49 X0
           grind)
        | exact superpose b0e49 b0e77
        | (have j0 := b0e77 X0 X1
           grind)
        | exact resolve b0e77 b0e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e77
      have b0e90 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e83 X0 X1
           have j1 := b0e81 X1 X0
           grind)
        | (have r₁ := b0e83 X0 X1
           have r₂ := b0e81 X0 X1
           grind)
        | (have r₁ := b0e83 X1 X0
           have r₂ := b0e81 X0 X1
           grind)
        | (have r₁ := b0e83 X1 X1
           have r₂ := b0e81 X1 X1
           grind)
        | exact resolve b0e83 b0e81
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e81 b0e83
      have b0e94 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e88 X0 X1
           have i₂ := b0e49 X1
           grind)
        | exact superpose b0e49 b0e88
        | (have j0 := b0e88 X0 X1
           grind)
        | exact resolve b0e88 b0e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e88
      have b0e118 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e27 X1 (τ X0)
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e27
        | exact resolve b0e27 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e170 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 X1 (σ X0)
           have i₂ := b0e49 X0
           grind)
        | exact superpose b0e49 b0e14
        | (have j0 := b0e14 X1 (σ X0)
           grind)
        | exact resolve b0e14 b0e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e171 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 (σ X0) X1
           have i₂ := b0e49 X0
           grind)
        | exact superpose b0e49 b0e15
        | (have j0 := b0e15 (σ X0) X1
           grind)
        | exact resolve b0e15 b0e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e252 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e12 (M.op (τ X0) (τ X0))
           have i₂ := b0e51 X0
           grind)
        | exact superpose b0e51 b0e12
        | exact resolve b0e12 b0e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e343 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e22 X0 X1
           have i₂ := b0e90 X1 (τ X0)
           grind)
        | exact superpose b0e90 b0e22
        | (have j1 := b0e90 X1 (τ X0)
           grind)
        | exact resolve b0e22 b0e90
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e90
      have b0e370 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e343 X0 X1
           have i₂ := b0e51 X0
           grind)
        | exact superpose b0e51 b0e343
        | (have j0 := b0e343 X0 X1
           grind)
        | exact resolve b0e343 b0e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e343
      have b0e390 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e370 X0 X1
           have i₂ := b0e252 X0
           grind)
        | exact superpose b0e252 b0e370
        | (have j0 := b0e370 X0 X1
           grind)
        | exact resolve b0e370 b0e252
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e370
      have b0e411 : ∀ X0 X1 : G, (M.op (τ X0) X1) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (τ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 X1 (τ X0)
           have i₂ := b0e252 X0
           grind)
        | exact superpose b0e252 b0e14
        | (have j0 := b0e14 X1 (τ X0)
           grind)
        | exact resolve b0e14 b0e252
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e252
      have b0e996 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 (σ X0) (σ X1)
           have i₂ := b0e94 X1 X0
           grind)
        | exact superpose b0e94 b0e14
        | (have j0 := b0e14 (σ X0) (σ X1)
           have j1 := b0e94 X1 X0
           grind)
        | exact resolve b0e14 b0e94
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1011 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e94 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1012 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e94 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e94
      have b0e1058 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have j0 := b0e996 X0 X1
           have j1 := b0e170 X1 (σ X0)
           grind)
        | (have r₁ := b0e996 X0 X0
           have r₂ := b0e170 X0 (σ X0)
           grind)
        | (have r₁ := b0e996 X0 X0
           have r₂ := b0e170 X0 (σ X0)
           grind)
        | exact resolve b0e996 b0e170
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e170 b0e996
      have b0e1111 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e1058 X0 X1
           have i₂ := b0e49 X1
           grind)
        | exact superpose b0e49 b0e1058
        | (have j0 := b0e1058 X0 X1
           grind)
        | exact resolve b0e1058 b0e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1058
      have b0e1146 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e1111 X0 X1
           have i₂ := b0e49 X0
           grind)
        | exact superpose b0e49 b0e1111
        | (have j0 := b0e1111 X0 X1
           grind)
        | exact resolve b0e1111 b0e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1111
      have b0e1167 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e1146 X0 X1
           have i₂ := b0e17 X0 X1
           grind)
        | exact superpose b0e17 b0e1146
        | (have j0 := b0e1146 X0 X1
           grind)
        | exact resolve b0e1146 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1146
      have b0e9975 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e411 X0 X1
           have i₂ := b0e390 X0 X1
           grind)
        | exact superpose b0e390 b0e411
        | (have j0 := b0e411 X0 X1
           have j1 := b0e390 X0 X1
           grind)
        | (have r₁ := b0e411 X0 X1
           have r₂ := b0e390 X0 X1
           grind)
        | exact resolve b0e411 b0e390
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e390 b0e411
      have b0e10207 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
        intro X0 X1
        first
        | (have j0 := b0e9975 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9975
      have b0e12239 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e76 (σ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e76
        | exact resolve b0e76 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e76
      have b0e12744 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e12239 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e12239
        | (have j0 := b0e12239 X0 X1
           grind)
        | exact resolve b0e12239 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e12239
      have b0e15904 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e1167 (τ X1) (τ X0)
           have i₂ := b0e118 X0 X1
           grind)
        | exact superpose b0e118 b0e1167
        | (have j0 := b0e1167 (τ X0) (τ X1)
           grind)
        | exact resolve b0e1167 b0e118
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1167
      have b0e16004 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e15904 X0 X1
           have i₂ := b0e13 (k X0 X1)
           grind)
        | exact superpose b0e13 b0e15904
        | (have j0 := b0e15904 X0 X1
           grind)
        | exact resolve b0e15904 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e15904
      have b0e16039 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e16004 X0 X1
           have i₂ := b0e51 X1
           grind)
        | exact superpose b0e51 b0e16004
        | (have j0 := b0e16004 X0 X1
           grind)
        | exact resolve b0e16004 b0e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e16004
      have b0e16070 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e16039 X0 X1
           have i₂ := b0e13 (k X0 X1)
           grind)
        | exact superpose b0e13 b0e16039
        | (have j0 := b0e16039 X0 X1
           grind)
        | exact resolve b0e16039 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e16039
      have b0e16090 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e16070 X0 X1
           have i₂ := b0e51 X0
           grind)
        | exact superpose b0e51 b0e16070
        | (have j0 := b0e16070 X0 X1
           grind)
        | exact resolve b0e16070 b0e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e16070
      have b0e16103 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e16090 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e16090
        | (have j0 := b0e16090 X0 X1
           grind)
        | exact resolve b0e16090 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e16090
      have b0e16111 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e16103 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e16103
        | (have j0 := b0e16103 X0 X1
           grind)
        | exact resolve b0e16103 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e16103
      have b0e16115 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e16111 X0 X1
           have i₂ := b0e51 X0
           grind)
        | exact superpose b0e51 b0e16111
        | (have j0 := b0e16111 X0 X1
           grind)
        | exact resolve b0e16111 b0e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e16111
      have b0e134327 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (τ X1)) (σ X0)) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e1012 (τ X1) X0
           have i₂ := b0e10207 X1 X0
           grind)
        | exact superpose b0e10207 b0e1012
        | (have j0 := b0e1012 (τ X1) X0
           have j1 := b0e10207 X1 X0
           grind)
        | exact resolve b0e1012 b0e10207
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1012
      have b0e134376 : ∀ X0 X1 : G, (k X0 (σ (τ X1))) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e21 X0 (τ X1)
           have i₂ := b0e10207 X1 (τ X0)
           grind)
        | exact superpose b0e10207 b0e21
        | (have j1 := b0e10207 X1 (τ X0)
           grind)
        | exact resolve b0e21 b0e10207
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21
      have b0e134933 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e27 (σ X1) X0
           have i₂ := b0e10207 (σ X0) X1
           grind)
        | exact superpose b0e10207 b0e27
        | (have j1 := b0e10207 (σ X0) X1
           grind)
        | exact resolve b0e27 b0e10207
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e10207
      have b0e135044 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (τ X1)) (σ X0)) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
        intro X0 X1
        first
        | (have j0 := b0e134327 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e134327
      have b0e135172 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e134933 X0 X1
           have i₂ := b0e12 X1
           grind)
        | exact superpose b0e12 b0e134933
        | (have j0 := b0e134933 X0 X1
           grind)
        | exact resolve b0e134933 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e134933
      have b0e135382 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ (τ X1))) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e134376 X0 X1
           have i₂ := b0e51 X0
           grind)
        | exact superpose b0e51 b0e134376
        | (have j0 := b0e134376 X0 X1
           grind)
        | exact resolve b0e134376 b0e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e134376
      have b0e135419 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ X0)) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e135044 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e135044
        | (have j0 := b0e135044 X0 X1
           grind)
        | exact resolve b0e135044 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e135044
      have b0e135717 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e135172 X0 X1
           have i₂ := b0e49 X0
           grind)
        | exact superpose b0e49 b0e135172
        | (have j0 := b0e135172 X0 X1
           grind)
        | exact resolve b0e135172 b0e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e135172
      have b0e135805 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e135382 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e135382
        | (have j0 := b0e135382 X0 X1
           grind)
        | exact resolve b0e135382 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e135382
      have b0e135838 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op X0 X0)) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e135419 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e135419
        | (have j0 := b0e135419 X0 X1
           grind)
        | exact resolve b0e135419 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e135419
      have b0e135987 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e135717 X0 X1
           have i₂ := b0e12 (M.op X0 X0)
           grind)
        | exact superpose b0e12 b0e135717
        | (have j0 := b0e135717 X0 X1
           grind)
        | exact resolve b0e135717 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e135717
      have b0e136052 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e135805 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e135805
        | (have j0 := b0e135805 X0 X1
           grind)
        | exact resolve b0e135805 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e135805
      have b0e136077 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e135838 X0 X1
           have i₂ := b0e51 X1
           grind)
        | exact superpose b0e51 b0e135838
        | (have j0 := b0e135838 X0 X1
           grind)
        | exact resolve b0e135838 b0e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e51 b0e135838
      have b0e136158 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e135987 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e135987
        | (have j0 := b0e135987 X0 X1
           grind)
        | exact resolve b0e135987 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e135987
      have b0e136213 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e136052 X0 X1
           have i₂ := b0e118 X1 X0
           grind)
        | exact superpose b0e118 b0e136052
        | (have j0 := b0e136052 X0 X1
           grind)
        | exact resolve b0e136052 b0e118
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e118 b0e136052
      have b0e136214 : ∀ X0 X1 : G, (M.op X1 X1) = (k (σ X0) X1) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
        intro X0 X1
        first
        | (have j0 := b0e136077 X0 X1
           have j1 := b0e171 X0 X1
           grind)
        | (have r₁ := b0e136077 X0 X1
           have r₂ := b0e171 X0 X1
           grind)
        | exact resolve b0e136077 b0e171
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e171 b0e136077
      have b0e136262 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e136158 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e136158
        | (have j0 := b0e136158 X0 X1
           grind)
        | exact resolve b0e136158 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e136158
      have b0e141996 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) (σ X0))) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e27 X1 X0
           have i₂ := b0e136262 (σ X0) X1
           grind)
        | exact superpose b0e136262 b0e27
        | (have j1 := b0e136262 (σ X0) X1
           grind)
        | exact resolve b0e27 b0e136262
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e142181 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e136262 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e136262
      have b0e142486 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (σ (M.op X0 X0))) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e141996 X0 X1
           have i₂ := b0e49 X0
           grind)
        | exact superpose b0e49 b0e141996
        | (have j0 := b0e141996 X0 X1
           grind)
        | exact resolve b0e141996 b0e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e141996
      have b0e143233 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e142486 X0 X1
           have i₂ := b0e12 (M.op X0 X0)
           grind)
        | exact superpose b0e12 b0e142486
        | (have j0 := b0e142486 X0 X1
           grind)
        | exact resolve b0e142486 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e142486
      have b0e147908 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e142181 X0 X1
           have i₂ := b0e12744 X1 X0
           grind)
        | (have i₁ := b0e142181 X1 X1
           have i₂ := b0e12744 X0 X1
           grind)
        | exact superpose b0e12744 b0e142181
        | (have j0 := b0e142181 X0 X1
           have j1 := b0e12744 X1 X0
           grind)
        | (have r₁ := b0e142181 X1 X0
           have r₂ := b0e12744 X0 X1
           grind)
        | (have r₁ := b0e142181 X1 X1
           have r₂ := b0e12744 X1 X1
           grind)
        | exact resolve b0e142181 b0e12744
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e12744 b0e142181
      have b0e148009 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e147908 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e147908
      have b0e148190 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b0e148009 X0 X1
           have j1 := b0e14 X0 X1
           grind)
        | (have r₁ := b0e148009 X0 X1
           have r₂ := b0e14 X0 X1
           grind)
        | (have r₁ := b0e148009 X0 X0
           have r₂ := b0e14 X0 X0
           grind)
        | exact resolve b0e148009 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e148009
      have b0e162130 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e16115 X0 X1
           have i₂ := b0e136213 X0 X1
           grind)
        | exact superpose b0e136213 b0e16115
        | (have j0 := b0e16115 X1 X0
           have j1 := b0e136213 X1 X0
           grind)
        | (have r₁ := b0e16115 X0 X1
           have r₂ := b0e136213 X0 X1
           grind)
        | (have r₁ := b0e16115 X1 X1
           have r₂ := b0e136213 X1 X1
           grind)
        | exact resolve b0e16115 b0e136213
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e163024 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e136213 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e136213
      have b0e163086 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e162130 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e162130
      have b0e164071 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e163086 X0 X1
           have j1 := b0e163024 X1 X0
           grind)
        | (have r₁ := b0e163086 X0 X1
           have r₂ := b0e163024 X0 X1
           grind)
        | (have r₁ := b0e163086 X1 X0
           have r₂ := b0e163024 X0 X1
           grind)
        | (have r₁ := b0e163086 X1 X1
           have r₂ := b0e163024 X1 X1
           grind)
        | exact resolve b0e163086 b0e163024
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e163024 b0e163086
      have b0e190888 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (k X1 (σ X0))) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e164071 (σ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e164071
        | (have j0 := b0e164071 (σ X0) X1
           grind)
        | exact resolve b0e164071 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e164071
      have b0e190964 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e190888 X0 X1
           have i₂ := b0e27 X1 X0
           grind)
        | exact superpose b0e27 b0e190888
        | (have j0 := b0e190888 X0 X1
           grind)
        | exact resolve b0e190888 b0e27
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e190888
      have b0e223456 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e27 (σ X1) X0
           have i₂ := b0e136214 X1 (σ X0)
           grind)
        | exact superpose b0e136214 b0e27
        | (have j1 := b0e136214 X1 (σ X0)
           grind)
        | exact resolve b0e27 b0e136214
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27 b0e136214
      have b0e223461 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e223456 X0 X1
           have i₂ := b0e12 X1
           grind)
        | exact superpose b0e12 b0e223456
        | (have j0 := b0e223456 X0 X1
           grind)
        | exact resolve b0e223456 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e223456
      have b0e223477 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e223461 X0 X1
           have i₂ := b0e49 X0
           grind)
        | exact superpose b0e49 b0e223461
        | (have j0 := b0e223461 X0 X1
           grind)
        | exact resolve b0e223461 b0e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e223461
      have b0e223484 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e223477 X0 X1
           have i₂ := b0e12 (M.op X0 X0)
           grind)
        | exact superpose b0e12 b0e223477
        | (have j0 := b0e223477 X0 X1
           grind)
        | exact resolve b0e223477 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e223477
      have b0e223488 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e223484 X0 X1
           have i₂ := b0e49 X0
           grind)
        | exact superpose b0e49 b0e223484
        | (have j0 := b0e223484 X0 X1
           grind)
        | exact resolve b0e223484 b0e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e223484
      have b0e223489 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e223488 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e223488
        | (have j0 := b0e223488 X0 X1
           grind)
        | exact resolve b0e223488 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e223488
      have b0e229799 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k y x) ∨ (M.op x x) = (k y x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e223489 x y
           grind)
        | exact superpose b0e223489 b0e18
        | (have j1 := b0e223489 x y
           grind)
        | exact resolve b0e18 b0e223489
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e223489
      have b0e275363 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X1))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e33 X0 (σ X1)
           have i₂ := b0e143233 X1 (σ X0)
           grind)
        | exact superpose b0e143233 b0e33
        | (have j1 := b0e143233 X1 (σ X0)
           grind)
        | exact resolve b0e33 b0e143233
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e143233
      have b0e275433 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e275363 X0 X1
           have i₂ := b0e12 X1
           grind)
        | exact superpose b0e12 b0e275363
        | (have j0 := b0e275363 X0 X1
           grind)
        | exact resolve b0e275363 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e275363
      have b0e275462 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e275433 X0 X1
           have i₂ := b0e49 X0
           grind)
        | exact superpose b0e49 b0e275433
        | (have j0 := b0e275433 X0 X1
           grind)
        | exact resolve b0e275433 b0e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e275433
      have b0e275479 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e275462 X0 X1
           have i₂ := b0e12 (M.op X0 X0)
           grind)
        | exact superpose b0e12 b0e275462
        | (have j0 := b0e275462 X0 X1
           grind)
        | exact resolve b0e275462 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e275462
      have b0e275492 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e275479 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e275479
        | (have j0 := b0e275479 X0 X1
           grind)
        | exact resolve b0e275479 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e275479
      have b0e275497 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e275492 X0 X1
           have i₂ := b0e17 X0 X1
           grind)
        | exact superpose b0e17 b0e275492
        | (have j0 := b0e275492 X0 X1
           grind)
        | exact resolve b0e275492 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e275492
      have b0e287300 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e275497 y x
           grind)
        | exact superpose b0e275497 b0e18
        | (have j1 := b0e275497 y x
           grind)
        | exact resolve b0e18 b0e275497
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e275497
      have b0e287487 : (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) := by
        first
        | (have j1 := b0e148190 y x
           grind)
        | (have r₁ := b0e287300
           have r₂ := b0e148190 y x
           grind)
        | exact resolve b0e287300 b0e148190
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e148190 b0e287300
      have b0e291419 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b0e287487
           have i₂ := b0e16 y x
           grind)
        | exact superpose b0e16 b0e287487
        | (have j1 := b0e16 y x
           grind)
        | exact resolve b0e287487 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e291441 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op y y) = (k y x) := by
        first
        | (have i₁ := b0e16115 y x
           have i₂ := b0e287487
           grind)
        | exact superpose b0e287487 b0e16115
        | (have j0 := b0e16115 y x
           grind)
        | (have r₁ := b0e16115 y x
           have r₂ := b0e287487
           grind)
        | exact resolve b0e16115 b0e287487
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e16115
      have b0e291457 : (M.op y y) ≠ (M.op x x) ∨ (M.op y y) = (k y x) := by grind
      clear b0e287487
      have b0e291461 : (M.op y y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op y y) = (k y x) := by grind
      clear b0e291441
      have b0e291472 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
      clear b0e291419
      have b0e291479 : (M.op y y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
        first
        | (have r₁ := b0e291461
           have r₂ := b0e291457
           grind)
        | exact resolve b0e291461 b0e291457
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e291457 b0e291461
      have b0e299824 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b0e229799
           have i₂ := b0e291472
           grind)
        | exact superpose b0e291472 b0e229799
        | exact resolve b0e229799 b0e291472
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e229799 b0e291472
      have b0e299995 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
      clear b0e299824
      have b0e299996 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
      clear b0e299995
      have b0e304503 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b0e291479
           have i₂ := b0e299996
           grind)
        | exact superpose b0e299996 b0e291479
        | exact resolve b0e291479 b0e299996
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e291479 b0e299996
      have b0e304529 : (M.op x y) = (M.op y y) := by grind
      clear b0e304503
      have b0e306777 : (M.op y y) ≠ (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (M.op x x) = (k y x) := by
        first
        | (have i₁ := b0e15 y x
           have i₂ := b0e304529
           grind)
        | exact superpose b0e304529 b0e15
        | (have j0 := b0e15 y y
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e304529
           grind)
        | exact resolve b0e15 b0e304529
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e306820 : (M.op x x) = (k y x) ∨ (M.op y y) = (M.op x x) := by grind
      clear b0e306777
      have b0e747758 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e33 X0 (σ X1)
           have i₂ := b0e190964 X1 (σ X0)
           grind)
        | exact superpose b0e190964 b0e33
        | (have j1 := b0e190964 X1 (σ X0)
           grind)
        | exact resolve b0e33 b0e190964
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33 b0e190964
      have b0e747763 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e747758 X0 X1
           have i₂ := b0e12 X1
           grind)
        | exact superpose b0e12 b0e747758
        | (have j0 := b0e747758 X0 X1
           grind)
        | exact resolve b0e747758 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e747758
      have b0e747781 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X0))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e747763 X0 X1
           have i₂ := b0e49 X0
           grind)
        | exact superpose b0e49 b0e747763
        | (have j0 := b0e747763 X0 X1
           grind)
        | exact resolve b0e747763 b0e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e747763
      have b0e747792 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e747781 X0 X1
           have i₂ := b0e12 (M.op X0 X0)
           grind)
        | exact superpose b0e12 b0e747781
        | (have j0 := b0e747781 X0 X1
           grind)
        | exact resolve b0e747781 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e747781
      have b0e747798 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e747792 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e747792
        | (have j0 := b0e747792 X0 X1
           grind)
        | exact resolve b0e747792 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e747792
      have b0e747799 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e747798 X0 X1
           have i₂ := b0e49 X0
           grind)
        | exact superpose b0e49 b0e747798
        | (have j0 := b0e747798 X0 X1
           grind)
        | exact resolve b0e747798 b0e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e49 b0e747798
      have b0e756303 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (k y x) ∨ (M.op y y) = (k y x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e747799 y x
           grind)
        | exact superpose b0e747799 b0e18
        | (have j1 := b0e747799 y x
           grind)
        | exact resolve b0e18 b0e747799
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e747799
      have b0e756351 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (k y x) ∨ (M.op y y) = (k y x) := by
        first
        | (have i₁ := b0e756303
           have i₂ := b0e304529
           grind)
        | exact superpose b0e304529 b0e756303
        | exact resolve b0e756303 b0e304529
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e756303
      have b0e756352 : (M.op x y) = (k y x) ∨ (M.op y y) = (k y x) := by grind
      clear b0e756351
      have b0e756360 : (M.op y y) = (k y x) ∨ (M.op y y) = (k y x) := by
        first
        | (have i₁ := b0e756352
           have i₂ := b0e304529
           grind)
        | exact superpose b0e304529 b0e756352
        | exact resolve b0e756352 b0e304529
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e756352
      have b0e756361 : (M.op y y) = (k y x) := by grind
      clear b0e756360
      have b0e758337 : (M.op y y) = (M.op x x) ∨ (M.op y y) = (M.op x x) := by
        first
        | (have i₁ := b0e306820
           have i₂ := b0e756361
           grind)
        | exact superpose b0e756361 b0e306820
        | exact resolve b0e306820 b0e756361
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e306820
      have b0e758399 : (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
        first
        | (have i₁ := b0e1011 x y
           have i₂ := b0e756361
           grind)
        | exact superpose b0e756361 b0e1011
        | (have j0 := b0e1011 x y
           grind)
        | exact resolve b0e1011 b0e756361
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1011 b0e756361
      have b0e758425 : (σ (M.op x x)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
      clear b0e758399
      have b0e758451 : (M.op y y) = (M.op x x) := by grind
      clear b0e758337
      have b0e931517 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
        first
        | (have i₁ := b0e758425
           have i₂ := b0e758451
           grind)
        | exact superpose b0e758451 b0e758425
        | exact resolve b0e758425 b0e758451
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e758425 b0e758451
      have b0e931519 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
      clear b0e931517
      have b0e941225 : (σ (M.op x y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e931519
           grind)
        | exact superpose b0e931519 b0e18
        | exact resolve b0e18 b0e931519
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e931519
      have b0e941263 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e941225
           have i₂ := b0e304529
           grind)
        | exact superpose b0e304529 b0e941225
        | exact resolve b0e941225 b0e304529
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e304529 b0e941225
      have b0e941264 : False := by grind
      exact b0e941264
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : (M.op y x) = (M.op y y) := by grind
        have b1e21 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e47 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (k x y) := by
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
        have b1e48 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b1e15 (σ x) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e50 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e51 : (M.op (σ y) (σ x)) = (k (σ x) (σ x)) := by grind
        clear b1e48
        have b1e52 : (M.op x x) = (k x y) := by grind
        clear b1e47
        have b1e53 : (M.op (σ y) (σ x)) = (σ (k x x)) := by
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
        have b1e54 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e53
             have i₂ := b1e50 x
             grind)
          | exact superpose b1e50 b1e53
          | exact resolve b1e53 b1e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53
        have b1e56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e50 (σ X0)
             grind)
          | exact superpose b1e50 b1e18
          | exact resolve b1e18 b1e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e63 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e56 X0
             have i₂ := b1e50 X0
             grind)
          | exact superpose b1e50 b1e56
          | exact resolve b1e56 b1e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e50 b1e56
        have b1e69 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 X0) = (M.op X0 (σ x)) ∨ (M.op X0 X0) = (k (σ x) X0) := by
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
        have b1e72 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 X0) = (M.op X0 (σ x)) ∨ (M.op X0 X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e69 X0
             have i₂ := b1e54
             grind)
          | exact superpose b1e54 b1e69
          | (have j0 := b1e69 X0
             grind)
          | exact resolve b1e69 b1e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e69
        have b1e124 : (M.op (σ y) (σ y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e54
             grind)
          | exact superpose b1e54 b1e21
          | exact resolve b1e21 b1e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e127 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e124
             have i₂ := b1e63 y
             grind)
          | exact superpose b1e63 b1e124
          | exact resolve b1e124 b1e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e124
        have b1e588 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e72 (σ y)
             have i₂ := b1e54
             grind)
          | exact superpose b1e54 b1e72
          | (have j0 := b1e72 (σ y)
             grind)
          | (have r₁ := b1e72 (σ y)
             have r₂ := b1e54
             grind)
          | exact resolve b1e72 b1e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54 b1e72
        have b1e589 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b1e588
        have b1e590 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e589
             have i₂ := b1e63 y
             grind)
          | exact superpose b1e63 b1e589
          | exact resolve b1e589 b1e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e589
        have b1e593 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e590
             have r₂ := b1e127
             grind)
          | exact resolve b1e590 b1e127
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e590
        have b1e595 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e593
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e593
          | exact resolve b1e593 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e593
        have b1e596 : (M.op (σ y) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e595
             have i₂ := b1e52
             grind)
          | exact superpose b1e52 b1e595
          | exact resolve b1e595 b1e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52 b1e595
        have b1e597 : (σ (M.op x x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e596
             have i₂ := b1e63 y
             grind)
          | exact superpose b1e63 b1e596
          | exact resolve b1e596 b1e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e63 b1e596
        have b1e598 : False := by grind
        exact b1e598
      · have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op y x) = (M.op y y) := by grind
        have b2e21 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (M.op (σ y) (σ x)) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e46 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (k x y) := by
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
        have b2e47 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e48 : (M.op x x) = (k x y) := by grind
        clear b2e46
        have b2e50 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e47 (σ X0)
             grind)
          | exact superpose b2e47 b2e18
          | exact resolve b2e18 b2e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e57 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e50 X0
             have i₂ := b2e47 X0
             grind)
          | exact superpose b2e47 b2e50
          | exact resolve b2e50 b2e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e47 b2e50
        have b2e84 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 X0) = (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = (k (σ x) X0) := by
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
        have b2e143 : (M.op (σ y) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e57 x
             grind)
          | exact superpose b2e57 b2e22
          | exact resolve b2e22 b2e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57
        have b2e751 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e84 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e84
        have b2e752 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e751
             have r₂ := b2e21
             grind)
          | exact resolve b2e751 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e751
        have b2e753 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e752
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e752
          | exact resolve b2e752 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e752
        have b2e754 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e753
             have i₂ := b2e48
             grind)
          | exact superpose b2e48 b2e753
          | exact resolve b2e753 b2e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48 b2e753
        have b2e755 : False := by grind
        exact b2e755
  · rcases eq_or_ne (M.op x x) (M.op y x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : (M.op y x) ≠ (M.op y y) := by grind
        have b3e21 : (M.op y x) = (M.op x x) := by grind
        have b3e22 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e48 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b3e50 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e51 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b3e48
        have b3e53 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e51
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e51
          | exact resolve b3e51 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e51
        have b3e69 : ∀ X0 : G, (M.op y x) ≠ (M.op X0 x) ∨ (M.op X0 X0) = (M.op X0 x) ∨ (M.op X0 X0) = (k x X0) := by
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
        have b3e75 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b3e15 (σ x) (σ x)
             have i₂ := b3e53
             grind)
          | exact superpose b3e53 b3e15
          | exact resolve b3e15 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53
        have b3e76 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
        clear b3e75
        have b3e77 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b3e76
             have i₂ := b3e18 x x
             grind)
          | exact superpose b3e18 b3e76
          | exact resolve b3e76 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e76
        have b3e78 : (σ (k x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e77
             have i₂ := b3e50 x
             grind)
          | exact superpose b3e50 b3e77
          | exact resolve b3e77 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50 b3e77
        have b3e79 : (σ (k x y)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b3e78
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e78
          | exact resolve b3e78 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e78
        have b3e130 : (k x y) = (τ (σ (M.op y x))) := by
          first
          | (have i₁ := b3e13 (k x y)
             have i₂ := b3e79
             grind)
          | exact superpose b3e79 b3e13
          | exact resolve b3e13 b3e79
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e79
        have b3e131 : (M.op y x) = (k x y) := by
          first
          | (have i₁ := b3e130
             have i₂ := b3e13 (M.op y x)
             grind)
          | exact superpose b3e13 b3e130
          | exact resolve b3e130 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e130
        have b3e209 : (M.op y x) = (M.op y y) ∨ (M.op y y) = (k x y) := by
          first
          | (have j0 := b3e69 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e69
        have b3e210 : (M.op y y) = (k x y) := by
          first
          | (have r₁ := b3e209
             have r₂ := b3e20
             grind)
          | exact resolve b3e209 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e209
        have b3e213 : (M.op y x) = (M.op y y) := by
          first
          | (have i₁ := b3e131
             have i₂ := b3e210
             grind)
          | exact superpose b3e210 b3e131
          | exact resolve b3e131 b3e210
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e131 b3e210
        have b3e218 : False := by grind
        exact b3e218
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
        · have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : (M.op y x) ≠ (M.op y y) := by grind
          have b4e22 : (M.op y x) = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
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
          have b4e39 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b4e42 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
          have b4e62 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e64 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e62 (σ X0)
               grind)
            | exact superpose b4e62 b4e19
            | exact resolve b4e19 b4e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e67 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
            intro X0
            first
            | (have i₁ := b4e28 X0 (τ X0)
               have i₂ := b4e62 (τ X0)
               grind)
            | exact superpose b4e62 b4e28
            | exact resolve b4e28 b4e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e70 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e67 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e67
            | exact resolve b4e67 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e67
          have b4e73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e64 X0
               have i₂ := b4e62 X0
               grind)
            | exact superpose b4e62 b4e64
            | exact resolve b4e64 b4e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e64
          have b4e76 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e70 X0
               have i₂ := b4e62 X0
               grind)
            | exact superpose b4e62 b4e70
            | exact resolve b4e70 b4e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e62 b4e70
          have b4e98 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) := by
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
          have b4e112 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 X0 X0
               have i₂ := b4e18 X0 X1
               grind)
            | (have i₁ := b4e17 X0 X1
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e17
            | (have j0 := b4e17 X0 X1
               have j1 := b4e18 X0 X1
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
          have b4e115 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e28 X0 X1
               have i₂ := b4e18 X1 (τ X0)
               grind)
            | exact superpose b4e18 b4e28
            | (have j1 := b4e18 X1 (τ X0)
               grind)
            | exact resolve b4e28 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e116 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
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
          have b4e120 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e18 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e121 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e18 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e123 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e112 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e112
          have b4e126 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e98 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e98
          have b4e129 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e116 X0 X1
               have i₂ := b4e73 X0
               grind)
            | exact superpose b4e73 b4e116
            | (have j0 := b4e116 X0 X1
               grind)
            | exact resolve b4e116 b4e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e116
          have b4e132 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e123 X0 X1
               have j1 := b4e121 X1 X0
               grind)
            | (have r₁ := b4e123 X0 X1
               have r₂ := b4e121 X0 X1
               grind)
            | (have r₁ := b4e123 X1 X0
               have r₂ := b4e121 X0 X1
               grind)
            | (have r₁ := b4e123 X1 X1
               have r₂ := b4e121 X1 X1
               grind)
            | exact resolve b4e123 b4e121
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e121 b4e123
          have b4e138 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e129 X0 X1
               have i₂ := b4e73 X1
               grind)
            | exact superpose b4e73 b4e129
            | (have j0 := b4e129 X0 X1
               grind)
            | exact resolve b4e129 b4e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e129
          have b4e149 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X1 (σ X0)
               have i₂ := b4e73 X0
               grind)
            | exact superpose b4e73 b4e16
            | (have j0 := b4e16 X1 (σ X0)
               grind)
            | exact resolve b4e16 b4e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e184 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e14 (M.op (τ X0) (τ X0))
               have i₂ := b4e76 X0
               grind)
            | exact superpose b4e76 b4e14
            | exact resolve b4e14 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e256 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) (τ X0))) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e27 X0 X1
               have i₂ := b4e126 X1 (τ X0)
               grind)
            | exact superpose b4e126 b4e27
            | (have j1 := b4e126 X1 (τ X0)
               grind)
            | exact resolve b4e27 b4e126
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e264 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e256 X0 X1
               have i₂ := b4e76 X0
               grind)
            | exact superpose b4e76 b4e256
            | (have j0 := b4e256 X0 X1
               grind)
            | exact resolve b4e256 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e256
          have b4e281 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ X0)) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e264 X0 X1
               have i₂ := b4e184 X0
               grind)
            | exact superpose b4e184 b4e264
            | (have j0 := b4e264 X0 X1
               grind)
            | exact resolve b4e264 b4e184
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e264
          have b4e307 : ∀ X0 X1 : G, (M.op (τ X0) X1) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X1 (τ X0)
               have i₂ := b4e184 X0
               grind)
            | exact superpose b4e184 b4e16
            | (have j0 := b4e16 X1 (τ X0)
               grind)
            | exact resolve b4e16 b4e184
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e401 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e28 X0 X1
               have i₂ := b4e132 X1 (τ X0)
               grind)
            | exact superpose b4e132 b4e28
            | (have j1 := b4e132 X1 (τ X0)
               grind)
            | exact resolve b4e28 b4e132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28 b4e132
          have b4e427 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e401 X0 X1
               have i₂ := b4e76 X0
               grind)
            | exact superpose b4e76 b4e401
            | (have j0 := b4e401 X0 X1
               grind)
            | exact resolve b4e401 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e401
          have b4e448 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e427 X0 X1
               have i₂ := b4e184 X0
               grind)
            | exact superpose b4e184 b4e427
            | (have j0 := b4e427 X0 X1
               grind)
            | exact resolve b4e427 b4e184
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e184 b4e427
          have b4e1307 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 (σ X0) (σ X1)
               have i₂ := b4e138 X1 X0
               grind)
            | exact superpose b4e138 b4e16
            | (have j0 := b4e16 (σ X0) (σ X1)
               have j1 := b4e138 X1 X0
               grind)
            | exact resolve b4e16 b4e138
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e138
          have b4e1369 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e1307 X0 X1
               have j1 := b4e149 X1 (σ X0)
               grind)
            | (have r₁ := b4e1307 X0 X0
               have r₂ := b4e149 X0 (σ X0)
               grind)
            | (have r₁ := b4e1307 X0 X0
               have r₂ := b4e149 X0 (σ X0)
               grind)
            | exact resolve b4e1307 b4e149
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e149 b4e1307
          have b4e1422 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e1369 X0 X1
               have i₂ := b4e73 X1
               grind)
            | exact superpose b4e73 b4e1369
            | (have j0 := b4e1369 X0 X1
               grind)
            | exact resolve b4e1369 b4e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1369
          have b4e1457 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e1422 X0 X1
               have i₂ := b4e73 X0
               grind)
            | exact superpose b4e73 b4e1422
            | (have j0 := b4e1422 X0 X1
               grind)
            | exact resolve b4e1422 b4e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1422
          have b4e1478 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e1457 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e1457
            | (have j0 := b4e1457 X0 X1
               grind)
            | exact resolve b4e1457 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1457
          have b4e7719 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (k (τ X1) X0) = (M.op X0 (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e15 (M.op X1 X1)
               have i₂ := b4e281 X1 X0
               grind)
            | exact superpose b4e281 b4e15
            | (have j1 := b4e281 X1 X0
               grind)
            | exact resolve b4e15 b4e281
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e281
          have b4e9681 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e307 X0 X1
               have i₂ := b4e448 X0 X1
               grind)
            | exact superpose b4e448 b4e307
            | (have j0 := b4e307 X0 X1
               have j1 := b4e448 X0 X1
               grind)
            | (have r₁ := b4e307 X0 X1
               have r₂ := b4e448 X0 X1
               grind)
            | exact resolve b4e307 b4e448
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e307
          have b4e9732 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e15 (M.op X0 X0)
               have i₂ := b4e448 X0 X1
               grind)
            | exact superpose b4e448 b4e15
            | (have j1 := b4e448 X0 X1
               grind)
            | exact resolve b4e15 b4e448
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e448
          have b4e9909 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have j0 := b4e9681 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9681
          have b4e11253 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e115 (σ X0) X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e115
            | exact resolve b4e115 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e115
          have b4e11734 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e11253 X0 X1
               have i₂ := b4e19 X1 X0
               grind)
            | exact superpose b4e19 b4e11253
            | (have j0 := b4e11253 X0 X1
               grind)
            | exact resolve b4e11253 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e11253
          have b4e15823 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e1478 (τ X1) (τ X0)
               have i₂ := b4e42 X0 X1
               grind)
            | exact superpose b4e42 b4e1478
            | (have j0 := b4e1478 (τ X0) (τ X1)
               grind)
            | exact resolve b4e1478 b4e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1478
          have b4e15927 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e15823 X0 X1
               have i₂ := b4e15 (k X0 X1)
               grind)
            | exact superpose b4e15 b4e15823
            | (have j0 := b4e15823 X0 X1
               grind)
            | exact resolve b4e15823 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e15823
          have b4e15962 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e15927 X0 X1
               have i₂ := b4e76 X1
               grind)
            | exact superpose b4e76 b4e15927
            | (have j0 := b4e15927 X0 X1
               grind)
            | exact resolve b4e15927 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e15927
          have b4e15993 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e15962 X0 X1
               have i₂ := b4e15 (k X0 X1)
               grind)
            | exact superpose b4e15 b4e15962
            | (have j0 := b4e15962 X0 X1
               grind)
            | exact resolve b4e15962 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e15962
          have b4e16014 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e15993 X0 X1
               have i₂ := b4e76 X0
               grind)
            | exact superpose b4e76 b4e15993
            | (have j0 := b4e15993 X0 X1
               grind)
            | exact resolve b4e15993 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e15993
          have b4e16029 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e16014 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e16014
            | (have j0 := b4e16014 X0 X1
               grind)
            | exact resolve b4e16014 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e16014
          have b4e16039 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e16029 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e16029
            | (have j0 := b4e16029 X0 X1
               grind)
            | exact resolve b4e16029 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e16029
          have b4e16045 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e16039 X0 X1
               have i₂ := b4e76 X0
               grind)
            | exact superpose b4e76 b4e16039
            | (have j0 := b4e16039 X0 X1
               grind)
            | exact resolve b4e16039 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e16039
          have b4e128305 : ∀ X0 X1 : G, (k X0 (σ (τ X1))) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e27 X0 (τ X1)
               have i₂ := b4e9909 X1 (τ X0)
               grind)
            | exact superpose b4e9909 b4e27
            | (have j1 := b4e9909 X1 (τ X0)
               grind)
            | exact resolve b4e27 b4e9909
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27
          have b4e128851 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e32 (σ X1) X0
               have i₂ := b4e9909 (σ X0) X1
               grind)
            | exact superpose b4e9909 b4e32
            | (have j1 := b4e9909 (σ X0) X1
               grind)
            | exact resolve b4e32 b4e9909
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9909
          have b4e129087 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e128851 X0 X1
               have i₂ := b4e14 X1
               grind)
            | exact superpose b4e14 b4e128851
            | (have j0 := b4e128851 X0 X1
               grind)
            | exact resolve b4e128851 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e128851
          have b4e129298 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ (τ X1))) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e128305 X0 X1
               have i₂ := b4e76 X0
               grind)
            | exact superpose b4e76 b4e128305
            | (have j0 := b4e128305 X0 X1
               grind)
            | exact resolve b4e128305 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e76 b4e128305
          have b4e129621 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e129087 X0 X1
               have i₂ := b4e73 X0
               grind)
            | exact superpose b4e73 b4e129087
            | (have j0 := b4e129087 X0 X1
               grind)
            | exact resolve b4e129087 b4e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e129087
          have b4e129712 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e129298 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e129298
            | (have j0 := b4e129298 X0 X1
               grind)
            | exact resolve b4e129298 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e129298
          have b4e129889 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e129621 X0 X1
               have i₂ := b4e14 (M.op X0 X0)
               grind)
            | exact superpose b4e14 b4e129621
            | (have j0 := b4e129621 X0 X1
               grind)
            | exact resolve b4e129621 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e129621
          have b4e129957 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e129712 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e129712
            | (have j0 := b4e129712 X0 X1
               grind)
            | exact resolve b4e129712 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e129712
          have b4e130059 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e129889 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e129889
            | (have j0 := b4e129889 X0 X1
               grind)
            | exact resolve b4e129889 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e129889
          have b4e130115 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e129957 X0 X1
               have i₂ := b4e42 X1 X0
               grind)
            | exact superpose b4e42 b4e129957
            | (have j0 := b4e129957 X0 X1
               grind)
            | exact resolve b4e129957 b4e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42 b4e129957
          have b4e130163 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e130059 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e130059
            | (have j0 := b4e130059 X0 X1
               grind)
            | exact resolve b4e130059 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e130059
          have b4e132382 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e32 X1 X0
               have i₂ := b4e130163 (σ X0) X1
               grind)
            | exact superpose b4e130163 b4e32
            | (have j1 := b4e130163 (σ X0) X1
               grind)
            | exact resolve b4e32 b4e130163
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e132566 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e130163 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e130163
          have b4e132874 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e132382 X0 X1
               have i₂ := b4e73 X0
               grind)
            | exact superpose b4e73 b4e132382
            | (have j0 := b4e132382 X0 X1
               grind)
            | exact resolve b4e132382 b4e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e132382
          have b4e133618 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e132874 X0 X1
               have i₂ := b4e14 (M.op X0 X0)
               grind)
            | exact superpose b4e14 b4e132874
            | (have j0 := b4e132874 X0 X1
               grind)
            | exact resolve b4e132874 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e132874
          have b4e138103 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e132566 X0 X1
               have i₂ := b4e11734 X1 X0
               grind)
            | (have i₁ := b4e132566 X1 X1
               have i₂ := b4e11734 X0 X1
               grind)
            | exact superpose b4e11734 b4e132566
            | (have j0 := b4e132566 X0 X1
               have j1 := b4e11734 X1 X0
               grind)
            | (have r₁ := b4e132566 X1 X0
               have r₂ := b4e11734 X0 X1
               grind)
            | (have r₁ := b4e132566 X1 X1
               have r₂ := b4e11734 X1 X1
               grind)
            | exact resolve b4e132566 b4e11734
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e11734 b4e132566
          have b4e138194 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e138103 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e138103
          have b4e138368 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e138194 X0 X1
               have j1 := b4e16 X0 X1
               grind)
            | (have r₁ := b4e138194 X0 X1
               have r₂ := b4e16 X0 X1
               grind)
            | (have r₁ := b4e138194 X0 X0
               have r₂ := b4e16 X0 X0
               grind)
            | exact resolve b4e138194 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e138194
          have b4e154602 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e130115 X0 X1
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e130115
            | (have j1 := b4e18 X1 X0
               grind)
            | exact resolve b4e130115 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e155622 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e16045 X0 X1
               have i₂ := b4e130115 X0 X1
               grind)
            | exact superpose b4e130115 b4e16045
            | (have j0 := b4e16045 X1 X0
               have j1 := b4e130115 X1 X0
               grind)
            | (have r₁ := b4e16045 X0 X1
               have r₂ := b4e130115 X0 X1
               grind)
            | (have r₁ := b4e16045 X1 X1
               have r₂ := b4e130115 X1 X1
               grind)
            | exact resolve b4e16045 b4e130115
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e156504 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e130115 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e130115
          have b4e156563 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e155622 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e155622
          have b4e156924 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e154602 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e154602
          have b4e157530 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e156563 X0 X1
               have j1 := b4e156504 X1 X0
               grind)
            | (have r₁ := b4e156563 X0 X1
               have r₂ := b4e156504 X0 X1
               grind)
            | (have r₁ := b4e156563 X1 X0
               have r₂ := b4e156504 X0 X1
               grind)
            | (have r₁ := b4e156563 X1 X1
               have r₂ := b4e156504 X1 X1
               grind)
            | exact resolve b4e156563 b4e156504
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e156504 b4e156563
          have b4e167795 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 X1 X1
               have i₂ := b4e156924 X0 X1
               grind)
            | (have i₁ := b4e17 X1 X0
               have i₂ := b4e156924 X0 X1
               grind)
            | exact superpose b4e156924 b4e17
            | (have j0 := b4e17 X0 X1
               have j1 := b4e156924 X1 X0
               grind)
            | (have r₁ := b4e17 X1 X0
               have r₂ := b4e156924 X0 X1
               grind)
            | (have r₁ := b4e17 X1 X1
               have r₂ := b4e156924 X1 X1
               grind)
            | exact resolve b4e17 b4e156924
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e168767 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e156924 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e156924
          have b4e168792 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e167795 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e167795
          have b4e169181 : ∀ X0 X1 : G, (M.op (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e168792 X0 X1
               have j1 := b4e168767 X1 X0
               grind)
            | (have r₁ := b4e168792 X0 X1
               have r₂ := b4e168767 X0 X1
               grind)
            | (have r₁ := b4e168792 X1 X0
               have r₂ := b4e168767 X0 X1
               grind)
            | (have r₁ := b4e168792 X1 X1
               have r₂ := b4e168767 X1 X1
               grind)
            | exact resolve b4e168792 b4e168767
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e168767 b4e168792
          have b4e184007 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e157530 (σ X1) (σ X0)
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e157530
            | (have j0 := b4e157530 (σ X1) (σ X0)
               grind)
            | exact resolve b4e157530 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e157530
          have b4e184068 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e184007 X0 X1
               have i₂ := b4e73 X0
               grind)
            | exact superpose b4e73 b4e184007
            | (have j0 := b4e184007 X0 X1
               grind)
            | exact resolve b4e184007 b4e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e184007
          have b4e184089 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) X0) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e184068 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e184068
            | (have j0 := b4e184068 X0 X1
               grind)
            | exact resolve b4e184068 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e184068
          have b4e184097 : ∀ X0 X1 : G, (M.op X1 X0) = (τ (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e184089 X0 X1
               have i₂ := b4e14 X1
               grind)
            | exact superpose b4e14 b4e184089
            | (have j0 := b4e184089 X0 X1
               grind)
            | exact resolve b4e184089 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e184089
          have b4e184101 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e184097 X0 X1
               have i₂ := b4e14 (k X0 X1)
               grind)
            | exact superpose b4e14 b4e184097
            | (have j0 := b4e184097 X0 X1
               grind)
            | exact resolve b4e184097 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e184097
          have b4e184104 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e184101 X0 X1
               have i₂ := b4e73 X0
               grind)
            | exact superpose b4e73 b4e184101
            | (have j0 := b4e184101 X0 X1
               grind)
            | exact resolve b4e184101 b4e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e184101
          have b4e185659 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ X1) X0) ∨ (τ (M.op (σ X0) X1)) = (M.op (τ (σ X0)) (τ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e32 X1 X0
               have i₂ := b4e169181 X1 (σ X0)
               grind)
            | exact superpose b4e169181 b4e32
            | (have j1 := b4e169181 X1 (σ X0)
               grind)
            | exact resolve b4e32 b4e169181
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32 b4e169181
          have b4e185683 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = (k (τ X1) X0) ∨ (τ (M.op (σ X0) X1)) = (M.op (τ (σ X0)) (τ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e185659 X0 X1
               have i₂ := b4e73 X0
               grind)
            | exact superpose b4e73 b4e185659
            | (have j0 := b4e185659 X0 X1
               grind)
            | exact resolve b4e185659 b4e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e185659
          have b4e185697 : ∀ X0 X1 : G, (M.op X0 X0) = (k (τ X1) X0) ∨ (τ (M.op (σ X0) X1)) = (M.op (τ (σ X0)) (τ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e185683 X0 X1
               have i₂ := b4e14 (M.op X0 X0)
               grind)
            | exact superpose b4e14 b4e185683
            | (have j0 := b4e185683 X0 X1
               grind)
            | exact resolve b4e185683 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e185683
          have b4e185706 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (M.op X0 (τ X1)) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e185697 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e185697
            | (have j0 := b4e185697 X0 X1
               grind)
            | exact resolve b4e185697 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e185697
          have b4e185710 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) X1) ∨ (τ (M.op (σ X0) X1)) = (M.op X0 (τ X1)) ∨ (M.op X0 X0) = (k (τ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e185706 X0 X1
               have i₂ := b4e73 X0
               grind)
            | exact superpose b4e73 b4e185706
            | (have j0 := b4e185706 X0 X1
               grind)
            | exact resolve b4e185706 b4e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e185706
          have b4e223825 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e39 X0 (σ X1)
               have i₂ := b4e133618 X1 (σ X0)
               grind)
            | exact superpose b4e133618 b4e39
            | (have j1 := b4e133618 X1 (σ X0)
               grind)
            | exact resolve b4e39 b4e133618
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39 b4e133618
          have b4e223893 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e223825 X0 X1
               have i₂ := b4e73 X0
               grind)
            | exact superpose b4e73 b4e223825
            | (have j0 := b4e223825 X0 X1
               grind)
            | exact resolve b4e223825 b4e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e223825
          have b4e223922 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ (σ X1))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e223893 X0 X1
               have i₂ := b4e14 (M.op X0 X0)
               grind)
            | exact superpose b4e14 b4e223893
            | (have j0 := b4e223893 X0 X1
               grind)
            | exact resolve b4e223893 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e223893
          have b4e223939 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e223922 X0 X1
               have i₂ := b4e14 X1
               grind)
            | exact superpose b4e14 b4e223922
            | (have j0 := b4e223922 X0 X1
               grind)
            | exact resolve b4e223922 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e223922
          have b4e223952 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e223939 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e223939
            | (have j0 := b4e223939 X0 X1
               grind)
            | exact resolve b4e223939 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e223939
          have b4e223957 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e223952 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e223952
            | (have j0 := b4e223952 X0 X1
               grind)
            | exact resolve b4e223952 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e223952
          have b4e234082 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e223957 y x
               grind)
            | exact superpose b4e223957 b4e20
            | (have j1 := b4e223957 y x
               grind)
            | exact resolve b4e20 b4e223957
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e223957
          have b4e234255 : (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) := by
            first
            | (have j1 := b4e138368 y x
               grind)
            | (have r₁ := b4e234082
               have r₂ := b4e138368 y x
               grind)
            | exact resolve b4e234082 b4e138368
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e138368 b4e234082
          have b4e237988 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b4e234255
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e234255
            | (have j1 := b4e18 y x
               grind)
            | exact resolve b4e234255 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e234255
          have b4e238036 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
          clear b4e237988
          have b4e545778 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e7719 X0 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e7719
            | (have j0 := b4e7719 X1 (σ X0)
               grind)
            | exact resolve b4e7719 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7719
          have b4e545822 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e545778 X0 X1
               have i₂ := b4e73 X0
               grind)
            | exact superpose b4e73 b4e545778
            | (have j0 := b4e545778 X0 X1
               grind)
            | exact resolve b4e545778 b4e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e545778
          have b4e545825 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e545822 X0 X1
               have i₂ := b4e73 X0
               grind)
            | exact superpose b4e73 b4e545822
            | (have j0 := b4e545822 X0 X1
               grind)
            | exact resolve b4e545822 b4e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e545822
          have b4e545828 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e545825 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e545825
            | (have j0 := b4e545825 X0 X1
               grind)
            | exact resolve b4e545825 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e545825
          have b4e555393 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (k X1 X0) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e9732 (σ X0) X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e9732
            | (have j0 := b4e9732 (σ X0) X1
               grind)
            | exact resolve b4e9732 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9732
          have b4e555437 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (k X1 X0) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e555393 X0 X1
               have i₂ := b4e73 X0
               grind)
            | exact superpose b4e73 b4e555393
            | (have j0 := b4e555393 X0 X1
               grind)
            | exact resolve b4e555393 b4e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e555393
          have b4e555441 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e555437 X0 X1
               have i₂ := b4e73 X0
               grind)
            | exact superpose b4e73 b4e555437
            | (have j0 := b4e555437 X0 X1
               grind)
            | exact resolve b4e555437 b4e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e73 b4e555437
          have b4e555445 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e555441 X0 X1
               have i₂ := b4e19 X1 X0
               grind)
            | exact superpose b4e19 b4e555441
            | (have j0 := b4e555441 X0 X1
               grind)
            | exact resolve b4e555441 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e555441
          have b4e565650 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (k X0 X1))) ∨ (σ (M.op X1 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (M.op X1 X1)
               have i₂ := b4e555445 X1 X0
               grind)
            | exact superpose b4e555445 b4e14
            | (have j1 := b4e555445 X1 X0
               grind)
            | exact resolve b4e14 b4e555445
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e555445
          have b4e565686 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e565650 X0 X1
               have i₂ := b4e14 (k X0 X1)
               grind)
            | exact superpose b4e14 b4e565650
            | (have j0 := b4e565650 X0 X1
               grind)
            | exact resolve b4e565650 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e565650
          have b4e1013030 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (k y x) ∨ (σ (M.op y y)) = (σ (k y x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e184104 y x
               grind)
            | exact superpose b4e184104 b4e20
            | (have j1 := b4e184104 y x
               grind)
            | exact resolve b4e20 b4e184104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e184104
          have b4e1013040 : (σ (M.op y y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
            first
            | (have j1 := b4e545828 y x
               grind)
            | (have r₁ := b4e1013030
               have r₂ := b4e545828 y x
               grind)
            | exact resolve b4e1013030 b4e545828
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e545828 b4e1013030
          have b4e1016929 : (k y x) = (τ (σ (M.op y y))) ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b4e14 (k y x)
               have i₂ := b4e1013040
               grind)
            | exact superpose b4e1013040 b4e14
            | exact resolve b4e14 b4e1013040
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1013040
          have b4e1016983 : (M.op y y) = (k y x) ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b4e1016929
               have i₂ := b4e14 (M.op y y)
               grind)
            | exact superpose b4e14 b4e1016929
            | exact resolve b4e1016929 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1016929
          have b4e1018766 : (M.op x y) ≠ (M.op y y) ∨ (M.op x y) = (k y x) := by grind
          clear b4e1016983
          have b4e6746129 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e185710 X0 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e185710
            | (have j0 := b4e185710 X1 (σ X0)
               grind)
            | exact resolve b4e185710 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e185710
          have b4e6747913 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e15 (M.op (σ X0) (σ X1))
               have i₂ := b4e6746129 X1 X0
               grind)
            | exact superpose b4e6746129 b4e15
            | (have j1 := b4e6746129 X1 X0
               grind)
            | exact resolve b4e15 b4e6746129
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6746129
          have b4e6748562 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e6747913 x y
               grind)
            | exact superpose b4e6747913 b4e20
            | (have j1 := b4e6747913 x y
               grind)
            | (have r₁ := b4e20
               have r₂ := b4e6747913 x y
               grind)
            | exact resolve b4e20 b4e6747913
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6747913
          have b4e6748565 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (k y x) := by grind
          clear b4e6748562
          have b4e6748571 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e6748565
               grind)
            | exact superpose b4e6748565 b4e20
            | exact resolve b4e20 b4e6748565
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6748565
          have b4e6748602 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x x) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b4e6748571
               have i₂ := b4e565686 y x
               grind)
            | exact superpose b4e565686 b4e6748571
            | (have j1 := b4e565686 y x
               grind)
            | (have r₁ := b4e6748571
               have r₂ := b4e565686 y x
               grind)
            | exact resolve b4e6748571 b4e565686
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e565686 b4e6748571
          have b4e6748603 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (k y x) := by grind
          clear b4e6748602
          have b4e6748604 : (M.op x y) = (k y x) ∨ (M.op x x) = (k y x) := by grind
          clear b4e6748603
          have b4e6748619 : (M.op x y) = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b4e6748604
               have i₂ := b4e126 x y
               grind)
            | exact superpose b4e126 b4e6748604
            | (have j1 := b4e126 x y
               grind)
            | exact resolve b4e6748604 b4e126
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e126
          have b4e6748705 : (M.op x y) ≠ (M.op x x) ∨ (M.op x x) = (k y x) := by grind
          clear b4e6748604
          have b4e6748707 : (M.op x y) = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (M.op x y) = (k y x) := by grind
          clear b4e6748619
          have b4e6748723 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (k y x) := by
            first
            | (have j1 := b4e120 x y
               grind)
            | (have r₁ := b4e6748707
               have r₂ := b4e120 y x
               grind)
            | (have r₁ := b4e6748707
               have r₂ := b4e120 x y
               grind)
            | exact resolve b4e6748707 b4e120
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e120 b4e6748707
          have b4e6748725 : (M.op x y) = (k y x) := by
            first
            | (have r₁ := b4e6748723
               have r₂ := b4e1018766
               grind)
            | exact resolve b4e6748723 b4e1018766
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1018766 b4e6748723
          have b4e6749249 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b4e16045 y x
               have i₂ := b4e6748725
               grind)
            | exact superpose b4e6748725 b4e16045
            | (have j0 := b4e16045 y x
               grind)
            | exact resolve b4e16045 b4e6748725
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e16045
          have b4e6749287 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b4e6749249
          have b4e6749299 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b4e6749287
               have r₂ := b4e238036
               grind)
            | exact resolve b4e6749287 b4e238036
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e238036 b4e6749287
          have b4e6749313 : (M.op x y) ≠ (M.op x x) := by
            first
            | (have i₁ := b4e26
               have i₂ := b4e6749299
               grind)
            | exact superpose b4e6749299 b4e26
            | exact resolve b4e26 b4e6749299
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26
          have b4e6749433 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b4e17 y X0
               have i₂ := b4e6749299
               grind)
            | exact superpose b4e6749299 b4e17
            | (have j0 := b4e17 y X0
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e6749299
               grind)
            | exact resolve b4e17 b4e6749299
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6749299
          have b4e6754934 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) := by
            first
            | (have j0 := b4e6749433 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6749433
          have b4e6754935 : (M.op x x) = (k y x) := by
            first
            | (have r₁ := b4e6754934
               have r₂ := b4e6748705
               grind)
            | exact resolve b4e6754934 b4e6748705
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6748705 b4e6754934
          have b4e6755226 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b4e6748725
               have i₂ := b4e6754935
               grind)
            | exact superpose b4e6754935 b4e6748725
            | exact resolve b4e6748725 b4e6754935
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6748725 b4e6754935
          have b4e6755403 : False := by grind
          exact b4e6755403
        · have b5e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b5e61 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e63 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e61 (σ X0)
               grind)
            | exact superpose b5e61 b5e19
            | exact resolve b5e19 b5e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e72 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e63 X0
               have i₂ := b5e61 X0
               grind)
            | exact superpose b5e61 b5e63
            | exact resolve b5e63 b5e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61 b5e63
          have b5e80 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (M.op x x) ∨ (M.op y y) = (k x y) := by
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
          have b5e83 : (M.op y y) = (M.op x x) ∨ (M.op y y) = (k x y) := by grind
          clear b5e80
          have b5e84 : (M.op y y) = (k x y) := by
            first
            | (have r₁ := b5e83
               have r₂ := b5e25
               grind)
            | exact resolve b5e83 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e83
          have b5e98 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
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
          have b5e137 : (M.op (σ y) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e72 y
               grind)
            | exact superpose b5e72 b5e23
            | exact resolve b5e23 b5e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e72
          have b5e748 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e98 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e98
          have b5e749 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e748
               have r₂ := b5e24
               grind)
            | exact resolve b5e748 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e748
          have b5e751 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e749
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e749
            | exact resolve b5e749 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e749
          have b5e753 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e751
               have i₂ := b5e84
               grind)
            | exact superpose b5e84 b5e751
            | exact resolve b5e751 b5e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e84 b5e751
          have b5e754 : False := by grind
          exact b5e754
    · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op y x) ≠ (M.op y y) := by grind
        have b6e21 : (M.op y x) ≠ (M.op x x) := by grind
        have b6e22 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e46 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b6e47 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e48 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b6e46
        have b6e49 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
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
        have b6e69 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ x)
             have i₂ := b6e49
             grind)
          | exact superpose b6e49 b6e15
          | exact resolve b6e15 b6e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e49
        have b6e70 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
        clear b6e69
        have b6e71 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b6e70
             have i₂ := b6e18 x x
             grind)
          | exact superpose b6e18 b6e70
          | exact resolve b6e70 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e70
        have b6e72 : (σ (k x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e71
             have i₂ := b6e47 x
             grind)
          | exact superpose b6e47 b6e71
          | exact resolve b6e71 b6e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e47 b6e71
        have b6e124 : (k x y) = (τ (σ (M.op x x))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e72
             grind)
          | exact superpose b6e72 b6e13
          | exact resolve b6e13 b6e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e72
        have b6e125 : (M.op x x) = (k x y) := by
          first
          | (have i₁ := b6e124
             have i₂ := b6e13 (M.op x x)
             grind)
          | exact superpose b6e13 b6e124
          | exact resolve b6e124 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e124
        have b6e148 : (M.op y x) = (M.op x x) ∨ (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op x x) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e125
             grind)
          | exact superpose b6e125 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e125
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e125
        have b6e149 : (M.op y x) = (M.op x x) ∨ (M.op y x) = (M.op y y) := by grind
        clear b6e148
        have b6e151 : (M.op y x) = (M.op y y) := by
          first
          | (have r₁ := b6e149
             have r₂ := b6e21
             grind)
          | exact resolve b6e149 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e149
        have b6e153 : False := by grind
        exact b6e153
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b7e61 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e63 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e61 (σ X0)
               grind)
            | exact superpose b7e61 b7e19
            | exact resolve b7e19 b7e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e72 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e63 X0
               have i₂ := b7e61 X0
               grind)
            | exact superpose b7e61 b7e63
            | exact resolve b7e63 b7e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61 b7e63
          have b7e81 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
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
          have b7e83 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b7e81
          have b7e84 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e83
               have r₂ := b7e25
               grind)
            | exact resolve b7e83 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e83
          have b7e85 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e84
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e84
            | exact resolve b7e84 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e84
          have b7e86 : (σ (k x y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e85
               have i₂ := b7e72 y
               grind)
            | exact superpose b7e72 b7e85
            | exact resolve b7e85 b7e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72 b7e85
          have b7e91 : (k x y) = (τ (σ (M.op y y))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e86
               grind)
            | exact superpose b7e86 b7e14
            | exact resolve b7e14 b7e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e86
          have b7e92 : (M.op y y) = (k x y) := by
            first
            | (have i₁ := b7e91
               have i₂ := b7e14 (M.op y y)
               grind)
            | exact superpose b7e14 b7e91
            | exact resolve b7e91 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e91
          have b7e146 : (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op x x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e92
               grind)
            | exact superpose b7e92 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e92
          have b7e147 : (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op x x) := by grind
          clear b7e146
          have b7e149 : (M.op y x) = (M.op x x) := by
            first
            | (have r₁ := b7e147
               have r₂ := b7e21
               grind)
            | exact resolve b7e147 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e147
          have b7e151 : False := by grind
          exact b7e151
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b8e37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b8e40 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
          have b8e60 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e62 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e60 (σ X0)
               grind)
            | exact superpose b8e60 b8e19
            | exact resolve b8e19 b8e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e65 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
            intro X0
            first
            | (have i₁ := b8e26 X0 (τ X0)
               have i₂ := b8e60 (τ X0)
               grind)
            | exact superpose b8e60 b8e26
            | exact resolve b8e26 b8e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e68 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e65 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e65
            | exact resolve b8e65 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e65
          have b8e71 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e62 X0
               have i₂ := b8e60 X0
               grind)
            | exact superpose b8e60 b8e62
            | exact resolve b8e62 b8e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62
          have b8e74 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e68 X0
               have i₂ := b8e60 X0
               grind)
            | exact superpose b8e60 b8e68
            | exact resolve b8e68 b8e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60 b8e68
          have b8e86 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X1 (σ X0)
               have i₂ := b8e71 X0
               grind)
            | exact superpose b8e71 b8e16
            | (have j0 := b8e16 X1 (σ X0)
               grind)
            | exact resolve b8e16 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e99 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) := by
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
          have b8e115 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e17 X0 X0
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e17 X0 X1
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e17
            | (have j0 := b8e17 X0 X1
               have j1 := b8e18 X0 X1
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
          have b8e117 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
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
          have b8e119 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (M.op X0 (τ X1)) = (M.op (τ X1) (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e25 X1 X0
               have i₂ := b8e18 (τ X1) X0
               grind)
            | exact superpose b8e18 b8e25
            | (have j1 := b8e18 (τ X1) X0
               grind)
            | exact resolve b8e25 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e122 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e18 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e123 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e18 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e124 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e115 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e115
          have b8e127 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e99 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e99
          have b8e130 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e117 X0 X1
               have i₂ := b8e71 X0
               grind)
            | exact superpose b8e71 b8e117
            | (have j0 := b8e117 X0 X1
               grind)
            | exact resolve b8e117 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e117
          have b8e132 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e124 X0 X1
               have j1 := b8e123 X1 X0
               grind)
            | (have r₁ := b8e124 X0 X1
               have r₂ := b8e123 X0 X1
               grind)
            | (have r₁ := b8e124 X1 X0
               have r₂ := b8e123 X0 X1
               grind)
            | (have r₁ := b8e124 X1 X1
               have r₂ := b8e123 X1 X1
               grind)
            | exact resolve b8e124 b8e123
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e123 b8e124
          have b8e136 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e130 X0 X1
               have i₂ := b8e71 X1
               grind)
            | exact superpose b8e71 b8e130
            | (have j0 := b8e130 X0 X1
               grind)
            | exact resolve b8e130 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e130
          have b8e142 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e74 X0
               have i₂ := b8e18 X1 (τ X0)
               grind)
            | (have i₁ := b8e74 X0
               have i₂ := b8e18 (τ X0) (τ X0)
               grind)
            | exact superpose b8e18 b8e74
            | (have j1 := b8e18 X1 (τ X0)
               grind)
            | exact resolve b8e74 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e148 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e14 (M.op (τ X0) (τ X0))
               have i₂ := b8e74 X0
               grind)
            | exact superpose b8e74 b8e14
            | exact resolve b8e14 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e207 : ∀ X0 X1 : G, (M.op (τ X0) X1) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X1 (τ X0)
               have i₂ := b8e148 X0
               grind)
            | exact superpose b8e148 b8e16
            | (have j0 := b8e16 X1 (τ X0)
               grind)
            | exact resolve b8e16 b8e148
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e256 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) (τ X0))) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e25 X0 X1
               have i₂ := b8e127 X1 (τ X0)
               grind)
            | exact superpose b8e127 b8e25
            | (have j1 := b8e127 X1 (τ X0)
               grind)
            | exact resolve b8e25 b8e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e267 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e256 X0 X1
               have i₂ := b8e74 X0
               grind)
            | exact superpose b8e74 b8e256
            | (have j0 := b8e256 X0 X1
               grind)
            | exact resolve b8e256 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e256
          have b8e284 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ X0)) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e267 X0 X1
               have i₂ := b8e148 X0
               grind)
            | exact superpose b8e148 b8e267
            | (have j0 := b8e267 X0 X1
               grind)
            | exact resolve b8e267 b8e148
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e267
          have b8e410 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X0 X1
               have i₂ := b8e132 X1 (τ X0)
               grind)
            | exact superpose b8e132 b8e26
            | (have j1 := b8e132 X1 (τ X0)
               grind)
            | exact resolve b8e26 b8e132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e132
          have b8e430 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e410 X0 X1
               have i₂ := b8e74 X0
               grind)
            | exact superpose b8e74 b8e410
            | (have j0 := b8e410 X0 X1
               grind)
            | exact resolve b8e410 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e410
          have b8e451 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e430 X0 X1
               have i₂ := b8e148 X0
               grind)
            | exact superpose b8e148 b8e430
            | (have j0 := b8e430 X0 X1
               grind)
            | exact resolve b8e430 b8e148
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e148 b8e430
          have b8e1114 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 (σ X0) (σ X1)
               have i₂ := b8e136 X1 X0
               grind)
            | exact superpose b8e136 b8e16
            | (have j0 := b8e16 (σ X0) (σ X1)
               have j1 := b8e136 X1 X0
               grind)
            | exact resolve b8e16 b8e136
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1129 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e136 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e136
          have b8e1176 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b8e1114 X0 X1
               have j1 := b8e86 X1 (σ X0)
               grind)
            | (have r₁ := b8e1114 X0 X0
               have r₂ := b8e86 X0 (σ X0)
               grind)
            | (have r₁ := b8e1114 X0 X0
               have r₂ := b8e86 X0 (σ X0)
               grind)
            | exact resolve b8e1114 b8e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e86 b8e1114
          have b8e1229 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e1176 X0 X1
               have i₂ := b8e71 X1
               grind)
            | exact superpose b8e71 b8e1176
            | (have j0 := b8e1176 X0 X1
               grind)
            | exact resolve b8e1176 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1176
          have b8e1264 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e1229 X0 X1
               have i₂ := b8e71 X0
               grind)
            | exact superpose b8e71 b8e1229
            | (have j0 := b8e1229 X0 X1
               grind)
            | exact resolve b8e1229 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1229
          have b8e1285 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e1264 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e1264
            | (have j0 := b8e1264 X0 X1
               grind)
            | exact resolve b8e1264 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1264
          have b8e6230 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X0 (τ X1)) = (k (τ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e15 (M.op X1 X1)
               have i₂ := b8e284 X1 X0
               grind)
            | exact superpose b8e284 b8e15
            | (have j1 := b8e284 X1 X0
               grind)
            | exact resolve b8e15 b8e284
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e284
          have b8e7821 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e207 X0 X1
               have i₂ := b8e451 X0 X1
               grind)
            | exact superpose b8e451 b8e207
            | (have j0 := b8e207 X0 X1
               have j1 := b8e451 X0 X1
               grind)
            | (have r₁ := b8e207 X0 X1
               have r₂ := b8e451 X0 X1
               grind)
            | exact resolve b8e207 b8e451
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e207 b8e451
          have b8e8019 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have j0 := b8e7821 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7821
          have b8e8691 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e119 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e119
            | exact resolve b8e119 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e119
          have b8e9151 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e8691 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e8691
            | (have j0 := b8e8691 X0 X1
               grind)
            | exact resolve b8e8691 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8691
          have b8e13122 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e1285 (τ X1) (τ X0)
               have i₂ := b8e40 X0 X1
               grind)
            | exact superpose b8e40 b8e1285
            | (have j0 := b8e1285 (τ X0) (τ X1)
               grind)
            | exact resolve b8e1285 b8e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e13208 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e13122 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e13122
            | (have j0 := b8e13122 X0 X1
               grind)
            | exact resolve b8e13122 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13122
          have b8e13235 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e13208 X0 X1
               have i₂ := b8e74 X1
               grind)
            | exact superpose b8e74 b8e13208
            | (have j0 := b8e13208 X0 X1
               grind)
            | exact resolve b8e13208 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13208
          have b8e13258 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e13235 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e13235
            | (have j0 := b8e13235 X0 X1
               grind)
            | exact resolve b8e13235 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13235
          have b8e13271 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e13258 X0 X1
               have i₂ := b8e74 X0
               grind)
            | exact superpose b8e74 b8e13258
            | (have j0 := b8e13258 X0 X1
               grind)
            | exact resolve b8e13258 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13258
          have b8e13279 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e13271 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e13271
            | (have j0 := b8e13271 X0 X1
               grind)
            | exact resolve b8e13271 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13271
          have b8e13282 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e13279 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e13279
            | (have j0 := b8e13279 X0 X1
               grind)
            | exact resolve b8e13279 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13279
          have b8e13283 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e13282 X0 X1
               have i₂ := b8e74 X0
               grind)
            | exact superpose b8e74 b8e13282
            | (have j0 := b8e13282 X0 X1
               grind)
            | exact resolve b8e13282 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13282
          have b8e137927 : ∀ X0 X1 : G, (k X0 (σ (τ X1))) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e25 X0 (τ X1)
               have i₂ := b8e8019 X1 (τ X0)
               grind)
            | exact superpose b8e8019 b8e25
            | (have j1 := b8e8019 X1 (τ X0)
               grind)
            | exact resolve b8e25 b8e8019
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25
          have b8e138492 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e30 (σ X1) X0
               have i₂ := b8e8019 (σ X0) X1
               grind)
            | exact superpose b8e8019 b8e30
            | (have j1 := b8e8019 (σ X0) X1
               grind)
            | exact resolve b8e30 b8e8019
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8019
          have b8e138730 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e138492 X0 X1
               have i₂ := b8e14 X1
               grind)
            | exact superpose b8e14 b8e138492
            | (have j0 := b8e138492 X0 X1
               grind)
            | exact resolve b8e138492 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e138492
          have b8e138952 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ (τ X1))) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e137927 X0 X1
               have i₂ := b8e74 X0
               grind)
            | exact superpose b8e74 b8e137927
            | (have j0 := b8e137927 X0 X1
               grind)
            | exact resolve b8e137927 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e74 b8e137927
          have b8e139286 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e138730 X0 X1
               have i₂ := b8e71 X0
               grind)
            | exact superpose b8e71 b8e138730
            | (have j0 := b8e138730 X0 X1
               grind)
            | exact resolve b8e138730 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e138730
          have b8e139378 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e138952 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e138952
            | (have j0 := b8e138952 X0 X1
               grind)
            | exact resolve b8e138952 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e138952
          have b8e139555 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e139286 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e139286
            | (have j0 := b8e139286 X0 X1
               grind)
            | exact resolve b8e139286 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e139286
          have b8e139623 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e139378 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e139378
            | (have j0 := b8e139378 X0 X1
               grind)
            | exact resolve b8e139378 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e139378
          have b8e139725 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e139555 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e139555
            | (have j0 := b8e139555 X0 X1
               grind)
            | exact resolve b8e139555 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e139555
          have b8e139781 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e139623 X0 X1
               have i₂ := b8e40 X1 X0
               grind)
            | exact superpose b8e40 b8e139623
            | (have j0 := b8e139623 X0 X1
               grind)
            | exact resolve b8e139623 b8e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40 b8e139623
          have b8e139829 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e139725 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e139725
            | (have j0 := b8e139725 X0 X1
               grind)
            | exact resolve b8e139725 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e139725
          have b8e144372 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e30 X1 X0
               have i₂ := b8e139829 (σ X0) X1
               grind)
            | exact superpose b8e139829 b8e30
            | (have j1 := b8e139829 (σ X0) X1
               grind)
            | exact resolve b8e30 b8e139829
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e144560 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e139829 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e144563 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e139829 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e139829
          have b8e144872 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e144372 X0 X1
               have i₂ := b8e71 X0
               grind)
            | exact superpose b8e71 b8e144372
            | (have j0 := b8e144372 X0 X1
               grind)
            | exact resolve b8e144372 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e144372
          have b8e145636 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e144872 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e144872
            | (have j0 := b8e144872 X0 X1
               grind)
            | exact resolve b8e144872 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e144872
          have b8e146555 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e144560 X0 X1
               have i₂ := b8e9151 X0 X1
               grind)
            | (have i₁ := b8e144560 X0 X0
               have i₂ := b8e9151 X0 X1
               grind)
            | exact superpose b8e9151 b8e144560
            | (have j0 := b8e144560 X0 X1
               have j1 := b8e9151 X0 X1
               grind)
            | (have r₁ := b8e144560 X0 X1
               have r₂ := b8e9151 X0 X1
               grind)
            | (have r₁ := b8e144560 X0 X0
               have r₂ := b8e9151 X0 X0
               grind)
            | exact resolve b8e144560 b8e9151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9151 b8e144560
          have b8e146644 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e146555 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e146555
          have b8e146819 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b8e146644 X0 X1
               have j1 := b8e16 X0 X1
               grind)
            | (have r₁ := b8e146644 X0 X1
               have r₂ := b8e16 X0 X1
               grind)
            | (have r₁ := b8e146644 X0 X0
               have r₂ := b8e16 X0 X0
               grind)
            | exact resolve b8e146644 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e146644
          have b8e167175 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e139781 X0 X1
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e139781
            | (have j1 := b8e18 X1 X0
               grind)
            | exact resolve b8e139781 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e167300 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e13283 X0 X1
               have i₂ := b8e139781 X0 X1
               grind)
            | exact superpose b8e139781 b8e13283
            | (have j0 := b8e13283 X1 X0
               have j1 := b8e139781 X1 X0
               grind)
            | (have r₁ := b8e13283 X0 X1
               have r₂ := b8e139781 X0 X1
               grind)
            | (have r₁ := b8e13283 X1 X1
               have r₂ := b8e139781 X1 X1
               grind)
            | exact resolve b8e13283 b8e139781
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e167408 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e139781 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e139781
          have b8e167422 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e167300 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e167300
          have b8e167477 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e167175 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e167175
          have b8e167526 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e167422 X0 X1
               have j1 := b8e167408 X1 X0
               grind)
            | (have r₁ := b8e167422 X0 X1
               have r₂ := b8e167408 X0 X1
               grind)
            | (have r₁ := b8e167422 X1 X0
               have r₂ := b8e167408 X0 X1
               grind)
            | (have r₁ := b8e167422 X1 X1
               have r₂ := b8e167408 X1 X1
               grind)
            | exact resolve b8e167422 b8e167408
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e167408 b8e167422
          have b8e168661 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e17 X1 X1
               have i₂ := b8e167477 X0 X1
               grind)
            | (have i₁ := b8e17 X1 X0
               have i₂ := b8e167477 X0 X1
               grind)
            | exact superpose b8e167477 b8e17
            | (have j0 := b8e17 X0 X1
               have j1 := b8e167477 X1 X0
               grind)
            | (have r₁ := b8e17 X1 X0
               have r₂ := b8e167477 X0 X1
               grind)
            | (have r₁ := b8e17 X1 X1
               have r₂ := b8e167477 X1 X1
               grind)
            | exact resolve b8e17 b8e167477
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e168742 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e167477 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e167477
          have b8e168753 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e168661 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e168661
          have b8e168775 : ∀ X0 X1 : G, (M.op (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e168753 X0 X1
               have j1 := b8e168742 X1 X0
               grind)
            | (have r₁ := b8e168753 X0 X1
               have r₂ := b8e168742 X0 X1
               grind)
            | (have r₁ := b8e168753 X1 X0
               have r₂ := b8e168742 X0 X1
               grind)
            | (have r₁ := b8e168753 X1 X1
               have r₂ := b8e168742 X1 X1
               grind)
            | exact resolve b8e168753 b8e168742
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e168742 b8e168753
          have b8e177217 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e167526 (σ X1) (σ X0)
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e167526
            | (have j0 := b8e167526 (σ X1) (σ X0)
               grind)
            | exact resolve b8e167526 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e167526
          have b8e177278 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e177217 X0 X1
               have i₂ := b8e71 X0
               grind)
            | exact superpose b8e71 b8e177217
            | (have j0 := b8e177217 X0 X1
               grind)
            | exact resolve b8e177217 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e177217
          have b8e177299 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) X0) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e177278 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e177278
            | (have j0 := b8e177278 X0 X1
               grind)
            | exact resolve b8e177278 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e177278
          have b8e177307 : ∀ X0 X1 : G, (M.op X1 X0) = (τ (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e177299 X0 X1
               have i₂ := b8e14 X1
               grind)
            | exact superpose b8e14 b8e177299
            | (have j0 := b8e177299 X0 X1
               grind)
            | exact resolve b8e177299 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e177299
          have b8e177311 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e177307 X0 X1
               have i₂ := b8e14 (k X0 X1)
               grind)
            | exact superpose b8e14 b8e177307
            | (have j0 := b8e177307 X0 X1
               grind)
            | exact resolve b8e177307 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e177307
          have b8e177314 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e177311 X0 X1
               have i₂ := b8e71 X0
               grind)
            | exact superpose b8e71 b8e177311
            | (have j0 := b8e177311 X0 X1
               grind)
            | exact resolve b8e177311 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e177311
          have b8e189696 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ X1) X0) ∨ (τ (M.op (σ X0) X1)) = (M.op (τ (σ X0)) (τ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e30 X1 X0
               have i₂ := b8e168775 X1 (σ X0)
               grind)
            | exact superpose b8e168775 b8e30
            | (have j1 := b8e168775 X1 (σ X0)
               grind)
            | exact resolve b8e30 b8e168775
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30 b8e168775
          have b8e189720 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = (k (τ X1) X0) ∨ (τ (M.op (σ X0) X1)) = (M.op (τ (σ X0)) (τ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e189696 X0 X1
               have i₂ := b8e71 X0
               grind)
            | exact superpose b8e71 b8e189696
            | (have j0 := b8e189696 X0 X1
               grind)
            | exact resolve b8e189696 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e189696
          have b8e189734 : ∀ X0 X1 : G, (M.op X0 X0) = (k (τ X1) X0) ∨ (τ (M.op (σ X0) X1)) = (M.op (τ (σ X0)) (τ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e189720 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e189720
            | (have j0 := b8e189720 X0 X1
               grind)
            | exact resolve b8e189720 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e189720
          have b8e189743 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e189734 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e189734
            | (have j0 := b8e189734 X0 X1
               grind)
            | exact resolve b8e189734 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e189734
          have b8e189747 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) X1) ∨ (M.op X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op X0 X0) = (k (τ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e189743 X0 X1
               have i₂ := b8e71 X0
               grind)
            | exact superpose b8e71 b8e189743
            | (have j0 := b8e189743 X0 X1
               grind)
            | exact resolve b8e189743 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e189743
          have b8e251541 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e37 X0 (σ X1)
               have i₂ := b8e145636 X1 (σ X0)
               grind)
            | exact superpose b8e145636 b8e37
            | (have j1 := b8e145636 X1 (σ X0)
               grind)
            | exact resolve b8e37 b8e145636
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e37 b8e145636
          have b8e251609 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e251541 X0 X1
               have i₂ := b8e71 X0
               grind)
            | exact superpose b8e71 b8e251541
            | (have j0 := b8e251541 X0 X1
               grind)
            | exact resolve b8e251541 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e251541
          have b8e251638 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ (σ X1))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e251609 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e251609
            | (have j0 := b8e251609 X0 X1
               grind)
            | exact resolve b8e251609 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e251609
          have b8e251655 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e251638 X0 X1
               have i₂ := b8e14 X1
               grind)
            | exact superpose b8e14 b8e251638
            | (have j0 := b8e251638 X0 X1
               grind)
            | exact resolve b8e251638 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e251638
          have b8e251668 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e251655 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e251655
            | (have j0 := b8e251655 X0 X1
               grind)
            | exact resolve b8e251655 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e251655
          have b8e251673 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e251668 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e251668
            | (have j0 := b8e251668 X0 X1
               grind)
            | exact resolve b8e251668 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e251668
          have b8e262740 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e251673 y x
               grind)
            | exact superpose b8e251673 b8e20
            | (have j1 := b8e251673 y x
               grind)
            | exact resolve b8e20 b8e251673
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e251673
          have b8e262911 : (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) := by
            first
            | (have j1 := b8e146819 y x
               grind)
            | (have r₁ := b8e262740
               have r₂ := b8e146819 y x
               grind)
            | exact resolve b8e262740 b8e146819
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e146819 b8e262740
          have b8e266827 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e262911
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e262911
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e262911 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e262911
          have b8e266875 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
          clear b8e266827
          have b8e526744 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e142 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e142
            | exact resolve b8e142 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e142
          have b8e526821 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X1 X0) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e526744 X0 X1
               have i₂ := b8e71 X0
               grind)
            | exact superpose b8e71 b8e526744
            | (have j0 := b8e526744 X0 X1
               grind)
            | exact resolve b8e526744 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e526744
          have b8e527839 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (σ (M.op X1 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e17 X1 X1
               have i₂ := b8e526821 X0 X1
               grind)
            | (have i₁ := b8e17 X1 X0
               have i₂ := b8e526821 X0 X1
               grind)
            | exact superpose b8e526821 b8e17
            | (have j0 := b8e17 X0 X0
               have j1 := b8e526821 X1 X0
               grind)
            | (have r₁ := b8e17 X1 X0
               have r₂ := b8e526821 X0 X1
               grind)
            | (have r₁ := b8e17 X1 X1
               have r₂ := b8e526821 X1 X1
               grind)
            | exact resolve b8e17 b8e526821
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e526821
          have b8e527847 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (σ (M.op X1 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e527839 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e527839
          have b8e527860 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e527847 X0 X1
               have j1 := b8e144563 X0 X1
               grind)
            | (have r₁ := b8e527847 X0 X1
               have r₂ := b8e144563 X0 X1
               grind)
            | (have r₁ := b8e527847 X1 X0
               have r₂ := b8e144563 X0 X1
               grind)
            | exact resolve b8e527847 b8e144563
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e144563 b8e527847
          have b8e581782 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e6230 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e6230
            | (have j0 := b8e6230 X1 (σ X0)
               grind)
            | exact resolve b8e6230 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6230
          have b8e581828 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e581782 X0 X1
               have i₂ := b8e71 X0
               grind)
            | exact superpose b8e71 b8e581782
            | (have j0 := b8e581782 X0 X1
               grind)
            | exact resolve b8e581782 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e581782
          have b8e581832 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e581828 X0 X1
               have i₂ := b8e71 X0
               grind)
            | exact superpose b8e71 b8e581828
            | (have j0 := b8e581828 X0 X1
               grind)
            | exact resolve b8e581828 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e71 b8e581828
          have b8e581836 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e581832 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e581832
            | (have j0 := b8e581832 X0 X1
               grind)
            | exact resolve b8e581832 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e581832
          have b8e1045010 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (k y x) ∨ (σ (M.op y y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e177314 y x
               grind)
            | exact superpose b8e177314 b8e20
            | (have j1 := b8e177314 y x
               grind)
            | exact resolve b8e20 b8e177314
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e177314
          have b8e1045021 : (σ (M.op y y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
            first
            | (have j1 := b8e581836 y x
               grind)
            | (have r₁ := b8e1045010
               have r₂ := b8e581836 y x
               grind)
            | exact resolve b8e1045010 b8e581836
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e581836 b8e1045010
          have b8e1046691 : (k y x) = (τ (σ (M.op y y))) ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b8e14 (k y x)
               have i₂ := b8e1045021
               grind)
            | exact superpose b8e1045021 b8e14
            | exact resolve b8e14 b8e1045021
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1045021
          have b8e1046745 : (M.op y y) = (k y x) ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b8e1046691
               have i₂ := b8e14 (M.op y y)
               grind)
            | exact superpose b8e14 b8e1046691
            | exact resolve b8e1046691 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1046691
          have b8e1048417 : (M.op x y) ≠ (M.op y y) ∨ (M.op x y) = (k y x) := by grind
          clear b8e1046745
          have b8e6741893 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e189747 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e189747
            | (have j0 := b8e189747 X1 (σ X0)
               grind)
            | exact resolve b8e189747 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e189747
          have b8e6743601 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e15 (M.op (σ X0) (σ X1))
               have i₂ := b8e6741893 X1 X0
               grind)
            | exact superpose b8e6741893 b8e15
            | (have j1 := b8e6741893 X1 X0
               grind)
            | exact resolve b8e15 b8e6741893
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6741893
          have b8e6744173 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e6743601 x y
               grind)
            | exact superpose b8e6743601 b8e20
            | (have j1 := b8e6743601 x y
               grind)
            | (have r₁ := b8e20
               have r₂ := b8e6743601 x y
               grind)
            | exact resolve b8e20 b8e6743601
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6743601
          have b8e6744176 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (k y x) := by grind
          clear b8e6744173
          have b8e6744188 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e6744176
               grind)
            | exact superpose b8e6744176 b8e20
            | exact resolve b8e20 b8e6744176
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6744176
          have b8e6744217 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x x) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b8e6744188
               have i₂ := b8e527860 y x
               grind)
            | exact superpose b8e527860 b8e6744188
            | (have j1 := b8e527860 y x
               grind)
            | (have r₁ := b8e6744188
               have r₂ := b8e527860 y x
               grind)
            | exact resolve b8e6744188 b8e527860
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e527860 b8e6744188
          have b8e6744218 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (k y x) := by grind
          clear b8e6744217
          have b8e6744219 : (M.op x y) = (k y x) ∨ (M.op x x) = (k y x) := by grind
          clear b8e6744218
          have b8e6744231 : (M.op x y) = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e6744219
               have i₂ := b8e127 x y
               grind)
            | exact superpose b8e127 b8e6744219
            | (have j1 := b8e127 x y
               grind)
            | exact resolve b8e6744219 b8e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e127
          have b8e6744318 : (M.op x y) ≠ (M.op x x) ∨ (M.op x x) = (k y x) := by grind
          clear b8e6744219
          have b8e6744320 : (M.op x y) = (M.op y y) ∨ (M.op y y) = (M.op x x) ∨ (M.op x y) = (k y x) := by grind
          clear b8e6744231
          have b8e6744340 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (k y x) := by
            first
            | (have j1 := b8e122 x y
               grind)
            | (have r₁ := b8e6744320
               have r₂ := b8e122 y x
               grind)
            | (have r₁ := b8e6744320
               have r₂ := b8e122 x y
               grind)
            | exact resolve b8e6744320 b8e122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e122 b8e6744320
          have b8e6744344 : (M.op x y) = (k y x) := by
            first
            | (have r₁ := b8e6744340
               have r₂ := b8e1048417
               grind)
            | exact resolve b8e6744340 b8e1048417
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1048417 b8e6744340
          have b8e6744864 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e1129 x y
               have i₂ := b8e6744344
               grind)
            | exact superpose b8e6744344 b8e1129
            | (have j0 := b8e1129 x y
               grind)
            | exact resolve b8e1129 b8e6744344
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1129
          have b8e6744868 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e13283 y x
               have i₂ := b8e6744344
               grind)
            | exact superpose b8e6744344 b8e13283
            | (have j0 := b8e13283 y x
               grind)
            | exact resolve b8e13283 b8e6744344
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13283 b8e6744344
          have b8e6744908 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e6744868
          have b8e6744921 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b8e6744908
               have r₂ := b8e266875
               grind)
            | exact resolve b8e6744908 b8e266875
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e266875 b8e6744908
          have b8e6744922 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b8e6744864
               have r₂ := b8e20
               grind)
            | exact resolve b8e6744864 b8e20
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6744864
          have b8e6744926 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e6744922
               have i₂ := b8e6744921
               grind)
            | exact superpose b8e6744921 b8e6744922
            | exact resolve b8e6744922 b8e6744921
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6744922
          have b8e6744930 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
            first
            | (have r₁ := b8e6744926
               have r₂ := b8e20
               grind)
            | exact resolve b8e6744926 b8e20
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6744926
          have b8e6745033 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b8e17 y X0
               have i₂ := b8e6744921
               grind)
            | exact superpose b8e6744921 b8e17
            | (have j0 := b8e17 y X0
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e6744921
               grind)
            | exact resolve b8e17 b8e6744921
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e6747381 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) := by
            first
            | (have j0 := b8e6745033 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6745033
          have b8e6747382 : (M.op x x) = (k y x) := by
            first
            | (have r₁ := b8e6747381
               have r₂ := b8e6744318
               grind)
            | exact resolve b8e6747381 b8e6744318
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6744318 b8e6747381
          have b8e6747671 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b8e1285 y x
               have i₂ := b8e6747382
               grind)
            | exact superpose b8e6747382 b8e1285
            | (have j0 := b8e1285 y x
               grind)
            | exact resolve b8e1285 b8e6747382
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1285 b8e6747382
          have b8e6747819 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
          clear b8e6747671
          have b8e6747848 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b8e6747819
               have i₂ := b8e6744921
               grind)
            | exact superpose b8e6744921 b8e6747819
            | exact resolve b8e6747819 b8e6744921
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6747819
          have b8e6747860 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b8e6747848
               have r₂ := b8e6744930
               grind)
            | exact resolve b8e6747848 b8e6744930
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6744930 b8e6747848
          have b8e6747867 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e6747860
               have i₂ := b8e6744921
               grind)
            | exact superpose b8e6744921 b8e6747860
            | exact resolve b8e6747860 b8e6744921
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6744921 b8e6747860
          have b8e6747871 : False := by grind
          exact b8e6747871

/-- `Equation2301`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation2301 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2301 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2301.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x y) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
    · have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op x y) := by grind
      have b0e20 : (σ x) = (M.op (σ x) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e21 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e18
        | exact resolve b0e18 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e22 : (σ x) ≠ (σ x) := by
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
      have b0e23 : False := by grind
      exact b0e23
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op x y) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e26 : x ≠ x ∨ y = (k x y) := by
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
        have b1e28 : y = (k x y) := by grind
        clear b1e26
        have b1e43 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e46 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e43
        have b1e47 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e46
             have r₂ := b1e23
             grind)
          | exact resolve b1e46 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46
        have b1e48 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e47
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e47
          | exact resolve b1e47 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e49 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e48
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e48
          | exact resolve b1e48 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e48
        have b1e50 : False := by grind
        exact b1e50
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op x y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : x ≠ x ∨ y = (k x y) := by
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
        have b2e25 : y = (k x y) := by grind
        clear b2e24
        have b2e48 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e127 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e48 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48
        have b2e464 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e127 x y
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e127
          | (have j0 := b2e127 x y
             grind)
          | exact resolve b2e127 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e127
        have b2e467 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b2e464
        have b2e470 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e467
             have r₂ := b2e22
             grind)
          | exact resolve b2e467 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e467
        have b2e474 : False := by grind
        exact b2e474
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : x ≠ (M.op x y) := by grind
        have b3e21 : y = (M.op x y) := by grind
        have b3e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : x ≠ y := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e20
          | exact resolve b3e20 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
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
        have b3e25 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e24
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e24
          | exact resolve b3e24 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e27 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b3e28 : (σ y) = (k (σ x) (σ y)) := by grind
        clear b3e27
        have b3e29 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b3e28
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e28
          | exact resolve b3e28 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28
        have b3e42 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
        have b3e44 : x = y ∨ x = (k x y) := by grind
        clear b3e42
        have b3e45 : x = (k x y) := by
          first
          | (have r₁ := b3e44
             have r₂ := b3e23
             grind)
          | exact resolve b3e44 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e44
        have b3e48 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e29
             have i₂ := b3e45
             grind)
          | exact superpose b3e45 b3e29
          | exact resolve b3e29 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29 b3e45
        have b3e49 : False := by grind
        exact b3e49
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x y) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e27 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e28 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e27
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e27
            | exact resolve b4e27 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27
          have b4e29 : False := by grind
          exact b4e29
        · have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ (M.op x y) := by grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : x ≠ y := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e21
            | exact resolve b5e21 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e40 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
          have b5e43 : x = y ∨ x = (k x y) := by grind
          clear b5e40
          have b5e44 : x = (k x y) := by
            first
            | (have r₁ := b5e43
               have r₂ := b5e25
               grind)
            | exact resolve b5e43 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e43
          have b5e47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b5e115 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e47 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47
          have b5e474 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e115 x y
               have i₂ := b5e44
               grind)
            | exact superpose b5e44 b5e115
            | (have j0 := b5e115 x y
               grind)
            | exact resolve b5e115 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44 b5e115
          have b5e477 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b5e474
          have b5e480 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e477
               have r₂ := b5e24
               grind)
            | exact resolve b5e477 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e477
          have b5e484 : False := by grind
          exact b5e484
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op x y) := by grind
        have b6e21 : y ≠ (M.op x y) := by grind
        have b6e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e24 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b6e25 : (σ y) = (k (σ x) (σ y)) := by grind
        clear b6e24
        have b6e26 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b6e25
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e25
          | exact resolve b6e25 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e31 : (k x y) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e26
             grind)
          | exact superpose b6e26 b6e13
          | exact resolve b6e13 b6e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26
        have b6e32 : y = (k x y) := by
          first
          | (have i₁ := b6e31
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e31
          | exact resolve b6e31 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31
        have b6e47 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e32
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e32
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e32 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32
        have b6e49 : y = (M.op x y) ∨ x = (M.op x y) := by grind
        clear b6e47
        have b6e52 : x = (M.op x y) := by
          first
          | (have r₁ := b6e49
             have r₂ := b6e21
             grind)
          | exact resolve b6e49 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e49
        have b6e55 : False := by grind
        exact b6e55
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ (M.op x y) := by grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e37 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e39 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e37
          have b7e40 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e39
               have r₂ := b7e25
               grind)
            | exact resolve b7e39 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e39
          have b7e41 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e40
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e40
            | exact resolve b7e40 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40
          have b7e44 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e41
               grind)
            | exact superpose b7e41 b7e14
            | exact resolve b7e14 b7e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41
          have b7e45 : x = (k x y) := by
            first
            | (have i₁ := b7e44
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e44
            | exact resolve b7e44 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e55 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e45
               grind)
            | exact superpose b7e45 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e56 : x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b7e55
          have b7e58 : y = (M.op x y) := by
            first
            | (have r₁ := b7e56
               have r₂ := b7e21
               grind)
            | exact resolve b7e56 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e60 : False := by grind
          exact b7e60
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op x y) := by grind
          have b8e22 : y ≠ (M.op x y) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e97 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e43 x y
               grind)
            | exact superpose b8e43 b8e20
            | (have j1 := b8e43 x y
               grind)
            | exact resolve b8e20 b8e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43
          have b8e107 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e97
               have r₂ := b8e24
               grind)
            | exact resolve b8e97 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e97
          have b8e110 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e107
               have r₂ := b8e23
               grind)
            | exact resolve b8e107 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e107
          have b8e111 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e110
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e110
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e110 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e110
          have b8e112 : y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b8e111
          have b8e113 : x = (M.op x y) := by
            first
            | (have r₁ := b8e112
               have r₂ := b8e22
               grind)
            | exact resolve b8e112 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e112
          have b8e114 : False := by grind
          exact b8e114

/-- `Equation2301`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation2301 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2301 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2301.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e57 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e59 : False := by grind
      exact b0e59
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e20 : x = y := by grind
        have b1e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e27 : False := by grind
        exact b1e27
      · have b2e20 : x = y := by grind
        have b2e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e27 : False := by grind
        exact b2e27
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e20 : x ≠ y := by grind
        have b3e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e25 : x = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e13
          | exact resolve b3e13 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e26 : x = y := by
          first
          | (have i₁ := b3e25
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e25
          | exact resolve b3e25 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25
        have b3e27 : False := by grind
        exact b3e27
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 (M.op X1 X0))) X1) = X0 := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ y := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e34 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (M.op X0 (M.op X1 X0))) (M.op X1 X0)) (M.op X1 (M.op X0 (M.op X1 X0)))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 (M.op X1 (M.op X0 (M.op X1 X0)))
               have i₂ := b4e13 X0 X1
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e49 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b4e160 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e49 x y
               grind)
            | exact superpose b4e49 b4e20
            | (have j1 := b4e49 x y
               grind)
            | exact resolve b4e20 b4e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49
          have b4e166 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b4e160
               have r₂ := b4e23
               grind)
            | exact resolve b4e160 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e160
          have b4e523 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b4e166
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e166
            | (have j1 := b4e18 y x
               grind)
            | (have r₁ := b4e166
               have r₂ := b4e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b4e166
               have r₂ := b4e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b4e166 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e166
          have b4e524 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b4e523
          have b4e525 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e524
               have r₂ := b4e21
               grind)
            | exact resolve b4e524 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e524
          have b4e574 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e525
               grind)
            | exact superpose b4e525 b4e20
            | exact resolve b4e20 b4e525
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e577 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e17 (σ y) (σ x)
               have i₂ := b4e525
               grind)
            | exact superpose b4e525 b4e17
            | (have j0 := b4e17 (σ x) (σ y)
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e525
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e525
               grind)
            | exact resolve b4e17 b4e525
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e525
          have b4e579 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b4e577
          have b4e581 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e579
               have r₂ := b4e23
               grind)
            | exact resolve b4e579 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e579
          have b4e587 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e581
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e581
            | exact resolve b4e581 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e581
          have b4e666 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b4e587
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e587
            | (have j1 := b4e18 y x
               grind)
            | exact resolve b4e587 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e587
          have b4e687 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b4e666
          have b4e704 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b4e687
               have r₂ := b4e574
               grind)
            | exact resolve b4e687 b4e574
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e574 b4e687
          have b4e705 : x = (M.op x y) := by
            first
            | (have r₁ := b4e704
               have r₂ := b4e21
               grind)
            | exact resolve b4e704 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e704
          have b4e733 : x = (M.op (M.op (M.op x (M.op y x)) x) (M.op x (M.op y x))) := by
            first
            | (have i₁ := b4e34 y x
               have i₂ := b4e705
               grind)
            | exact superpose b4e705 b4e34
            | exact resolve b4e34 b4e705
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e735 : y = (M.op (M.op x (M.op y x)) x) := by
            first
            | (have i₁ := b4e13 y x
               have i₂ := b4e705
               grind)
            | exact superpose b4e705 b4e13
            | exact resolve b4e13 b4e705
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e737 : y = (M.op (M.op x y) x) := by
            first
            | (have i₁ := b4e735
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e735
            | exact resolve b4e735 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e735
          have b4e739 : x = (M.op (M.op (M.op x y) x) (M.op x y)) := by
            first
            | (have i₁ := b4e733
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e733
            | exact resolve b4e733 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e733
          have b4e743 : y = (M.op x x) := by
            first
            | (have i₁ := b4e737
               have i₂ := b4e705
               grind)
            | exact superpose b4e705 b4e737
            | exact resolve b4e737 b4e705
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e737
          have b4e744 : x = (M.op (M.op x x) x) := by
            first
            | (have i₁ := b4e739
               have i₂ := b4e705
               grind)
            | exact superpose b4e705 b4e739
            | exact resolve b4e739 b4e705
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e705 b4e739
          have b4e746 : x = (M.op y x) := by
            first
            | (have i₁ := b4e744
               have i₂ := b4e743
               grind)
            | exact superpose b4e743 b4e744
            | exact resolve b4e744 b4e743
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e743 b4e744
          have b4e747 : x = y := by
            first
            | (have i₁ := b4e746
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e746
            | exact resolve b4e746 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e746
          have b4e748 : False := by grind
          exact b4e748
        · have b5e13 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 (M.op X1 X0))) X1) = X0 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : x ≠ y := by grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e33 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (M.op X0 (M.op X1 X0))) (M.op X1 X0)) (M.op X1 (M.op X0 (M.op X1 X0)))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 (M.op X1 (M.op X0 (M.op X1 X0)))
               have i₂ := b5e13 X0 X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e44 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e124 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e44 x y
               grind)
            | exact superpose b5e44 b5e20
            | (have j1 := b5e44 x y
               grind)
            | exact resolve b5e20 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44
          have b5e130 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e124
               have r₂ := b5e23
               grind)
            | exact resolve b5e124 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e124
          have b5e451 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b5e130
               have i₂ := b5e18 y x
               grind)
            | exact superpose b5e18 b5e130
            | (have j1 := b5e18 y x
               grind)
            | (have r₁ := b5e130
               have r₂ := b5e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b5e130
               have r₂ := b5e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b5e130 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e130
          have b5e452 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b5e451
          have b5e453 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b5e452
               have r₂ := b5e21
               grind)
            | exact resolve b5e452 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e452
          have b5e455 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e453
               grind)
            | exact superpose b5e453 b5e20
            | exact resolve b5e20 b5e453
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e458 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b5e17 (σ y) (σ x)
               have i₂ := b5e453
               grind)
            | exact superpose b5e453 b5e17
            | (have j0 := b5e17 (σ x) (σ y)
               grind)
            | (have r₁ := b5e17 (σ y) (σ x)
               have r₂ := b5e453
               grind)
            | (have r₁ := b5e17 y x
               have r₂ := b5e453
               grind)
            | exact resolve b5e17 b5e453
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e453
          have b5e460 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b5e458
          have b5e461 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b5e460
               have r₂ := b5e23
               grind)
            | exact resolve b5e460 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e460
          have b5e462 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b5e461
               have i₂ := b5e19 y x
               grind)
            | exact superpose b5e19 b5e461
            | exact resolve b5e461 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e461
          have b5e532 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b5e462
               have i₂ := b5e18 y x
               grind)
            | exact superpose b5e18 b5e462
            | (have j1 := b5e18 y x
               grind)
            | exact resolve b5e462 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e462
          have b5e553 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b5e532
          have b5e570 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b5e553
               have r₂ := b5e455
               grind)
            | exact resolve b5e553 b5e455
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e455 b5e553
          have b5e571 : x = (M.op x y) := by
            first
            | (have r₁ := b5e570
               have r₂ := b5e21
               grind)
            | exact resolve b5e570 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e570
          have b5e615 : x = (M.op (M.op (M.op x (M.op y x)) x) (M.op x (M.op y x))) := by
            first
            | (have i₁ := b5e33 y x
               have i₂ := b5e571
               grind)
            | exact superpose b5e571 b5e33
            | exact resolve b5e33 b5e571
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e617 : y = (M.op (M.op x (M.op y x)) x) := by
            first
            | (have i₁ := b5e13 y x
               have i₂ := b5e571
               grind)
            | exact superpose b5e571 b5e13
            | exact resolve b5e13 b5e571
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e619 : y = (M.op (M.op x y) x) := by
            first
            | (have i₁ := b5e617
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e617
            | exact resolve b5e617 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e617
          have b5e621 : x = (M.op (M.op (M.op x y) x) (M.op x y)) := by
            first
            | (have i₁ := b5e615
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e615
            | exact resolve b5e615 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e615
          have b5e625 : y = (M.op x x) := by
            first
            | (have i₁ := b5e619
               have i₂ := b5e571
               grind)
            | exact superpose b5e571 b5e619
            | exact resolve b5e619 b5e571
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e619
          have b5e626 : x = (M.op (M.op x x) x) := by
            first
            | (have i₁ := b5e621
               have i₂ := b5e571
               grind)
            | exact superpose b5e571 b5e621
            | exact resolve b5e621 b5e571
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e571 b5e621
          have b5e628 : x = (M.op y x) := by
            first
            | (have i₁ := b5e626
               have i₂ := b5e625
               grind)
            | exact superpose b5e625 b5e626
            | exact resolve b5e626 b5e625
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e625 b5e626
          have b5e629 : x = y := by
            first
            | (have i₁ := b5e628
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e628
            | exact resolve b5e628 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e628
          have b5e630 : False := by grind
          exact b5e630
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e20 : x ≠ y := by grind
        have b6e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e25 : x = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 x
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
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e25
          | exact resolve b6e25 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e27 : False := by grind
        exact b6e27
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : y ≠ (M.op y x) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e41 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e43 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e41
          have b7e44 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e43
               have r₂ := b7e23
               grind)
            | exact resolve b7e43 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e43
          have b7e45 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e44
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e44
            | exact resolve b7e44 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e48 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e45
               grind)
            | exact superpose b7e45 b7e14
            | exact resolve b7e14 b7e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e49 : y = (k x y) := by
            first
            | (have i₁ := b7e48
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e48
            | exact resolve b7e48 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e59 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e49
               grind)
            | exact superpose b7e49 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e60 : y = (M.op y x) ∨ x = y := by grind
          clear b7e59
          have b7e62 : x = y := by
            first
            | (have r₁ := b7e60
               have r₂ := b7e22
               grind)
            | exact resolve b7e60 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60
          have b7e64 : False := by grind
          exact b7e64
        · have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e54 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e87 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e54 x y
               grind)
            | exact superpose b8e54 b8e20
            | (have j1 := b8e54 x y
               grind)
            | exact resolve b8e20 b8e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e91 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b8e54 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e54
          have b8e93 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e87
               have r₂ := b8e23
               grind)
            | exact resolve b8e87 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e87
          have b8e338 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e93
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e93
            | (have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e93
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e93
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e93 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e93
          have b8e339 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b8e338
          have b8e340 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e339
               have r₂ := b8e21
               grind)
            | exact resolve b8e339 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e339
          have b8e342 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e340
               grind)
            | exact superpose b8e340 b8e20
            | exact resolve b8e20 b8e340
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e345 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e340
               grind)
            | exact superpose b8e340 b8e17
            | (have j0 := b8e17 (σ x) (σ y)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e340
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e340
               grind)
            | exact resolve b8e17 b8e340
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e340
          have b8e347 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b8e345
          have b8e348 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e347
               have r₂ := b8e23
               grind)
            | exact resolve b8e347 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e347
          have b8e350 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e348
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e348
            | exact resolve b8e348 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e348
          have b8e415 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e350
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e350
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e350 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e350
          have b8e435 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b8e415
          have b8e451 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b8e435
               have r₂ := b8e342
               grind)
            | exact resolve b8e435 b8e342
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e342 b8e435
          have b8e452 : x = (M.op x y) := by
            first
            | (have r₁ := b8e451
               have r₂ := b8e21
               grind)
            | exact resolve b8e451 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e451
          have b8e492 : x ≠ x ∨ x = y ∨ x = (k y x) := by
            first
            | (have i₁ := b8e17 y x
               have i₂ := b8e452
               grind)
            | exact superpose b8e452 b8e17
            | (have j0 := b8e17 x y
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e452
               grind)
            | exact resolve b8e17 b8e452
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e494 : x = y ∨ x = (k y x) := by grind
          clear b8e492
          have b8e495 : x = (k y x) := by
            first
            | (have r₁ := b8e494
               have r₂ := b8e21
               grind)
            | exact resolve b8e494 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e494
          have b8e521 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e91 x y
               have i₂ := b8e495
               grind)
            | exact superpose b8e495 b8e91
            | (have j0 := b8e91 x y
               grind)
            | exact resolve b8e91 b8e495
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e91 b8e495
          have b8e524 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
          clear b8e521
          have b8e526 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e524
               have r₂ := b8e23
               grind)
            | exact resolve b8e524 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e524
          have b8e566 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e526
               grind)
            | exact superpose b8e526 b8e20
            | exact resolve b8e20 b8e526
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e526
          have b8e574 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b8e566
               have i₂ := b8e452
               grind)
            | exact superpose b8e452 b8e566
            | exact resolve b8e566 b8e452
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e452 b8e566
          have b8e575 : False := by grind
          exact b8e575
