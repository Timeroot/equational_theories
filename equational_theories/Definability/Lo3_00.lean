import equational_theories.Definability.AutBox3
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else if X = Y then X
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pxy_pxy_pyy_x_y_pyy_pxx_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  refine nh ?_
  have hinj : ∀ a b : G, σ a = σ b → a = b := fun a b h ↦ by
    have hh := hi1 a
    rw [h, hi1 b] at hh
    exact hh.symm
  have hdiag : ∀ c : G, σ (M.op c c) = M.op (σ c) (σ c) := fun c ↦ by
    have a1 := ht c c
    have a2 := hu c c
    have a3 := hv c c
    have a4 := hw c c
    have b1 := ht (σ c) (σ c)
    have b2 := hu (σ c) (σ c)
    have b3 := hv (σ c) (σ c)
    have b4 := hw (σ c) (σ c)
    have gc := hd c c
    grind
  rcases eq_or_ne x y with h | h
  · subst h
    exact hdiag x
  have hs : σ x ≠ σ y := fun hc ↦ h (hinj _ _ hc)
  have e1 := ht x y
  have e2 := hu x y
  have e3 := hv x y
  have e4 := hw x y
  have f1 := ht (σ x) (σ y)
  have f2 := hu (σ x) (σ y)
  have f3 := hv (σ x) (σ y)
  have f4 := hw (σ x) (σ y)
  have g := hd x y
  have dx := hdiag x
  have dy := hdiag y
  grind

/-- `x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else if X = Y then Y
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pxy_pxy_pyy_x_y_pyy_pxx_y_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = M.op b b ∨ a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  refine nh ?_
  have hinj : ∀ a b : G, σ a = σ b → a = b := fun a b h ↦ by
    have hh := hi1 a
    rw [h, hi1 b] at hh
    exact hh.symm
  have hdiag : ∀ c : G, σ (M.op c c) = M.op (σ c) (σ c) := fun c ↦ by
    have a1 := ht c c
    have a2 := hu c c
    have a3 := hv c c
    have a4 := hw c c
    have b1 := ht (σ c) (σ c)
    have b2 := hu (σ c) (σ c)
    have b3 := hv (σ c) (σ c)
    have b4 := hw (σ c) (σ c)
    have gc := hd c c
    grind
  rcases eq_or_ne x y with h | h
  · subst h
    exact hdiag x
  have hs : σ x ≠ σ y := fun hc ↦ h (hinj _ _ hc)
  have e1 := ht x y
  have e2 := hu x y
  have e3 := hv x y
  have e4 := hw x y
  have f1 := ht (σ x) (σ y)
  have f2 := hu (σ x) (σ y)
  have f3 := hv (σ x) (σ y)
  have f4 := hw (σ x) (σ y)
  have g := hd x y
  have dx := hdiag x
  have dy := hdiag y
  grind

/-- `x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if X = Y then X else if m(X,Y) = m(Y,Y) then m(X,X)
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pxy_x_y_pxy_pyy_pyy_x_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  refine nh ?_
  have hinj : ∀ a b : G, σ a = σ b → a = b := fun a b h ↦ by
    have hh := hi1 a
    rw [h, hi1 b] at hh
    exact hh.symm
  have hdiag : ∀ c : G, σ (M.op c c) = M.op (σ c) (σ c) := fun c ↦ by
    have a1 := ht c c
    have a2 := hu c c
    have a3 := hv c c
    have a4 := hw c c
    have b1 := ht (σ c) (σ c)
    have b2 := hu (σ c) (σ c)
    have b3 := hv (σ c) (σ c)
    have b4 := hw (σ c) (σ c)
    have gc := hd c c
    grind
  rcases eq_or_ne x y with h | h
  · subst h
    exact hdiag x
  have hs : σ x ≠ σ y := fun hc ↦ h (hinj _ _ hc)
  have e1 := ht x y
  have e2 := hu x y
  have e3 := hv x y
  have e4 := hw x y
  have f1 := ht (σ x) (σ y)
  have f2 := hu (σ x) (σ y)
  have f3 := hv (σ x) (σ y)
  have f4 := hw (σ x) (σ y)
  have g := hd x y
  have dx := hdiag x
  have dy := hdiag y
  grind

/-- `x □ y = if m(X,X) = m(Y,X) then m(Y,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else if X = Y then X
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pyx_pyx_pyy_x_y_pyy_pxx_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  refine nh ?_
  have hinj : ∀ a b : G, σ a = σ b → a = b := fun a b h ↦ by
    have hh := hi1 a
    rw [h, hi1 b] at hh
    exact hh.symm
  have hdiag : ∀ c : G, σ (M.op c c) = M.op (σ c) (σ c) := fun c ↦ by
    have a1 := ht c c
    have a2 := hu c c
    have a3 := hv c c
    have a4 := hw c c
    have b1 := ht (σ c) (σ c)
    have b2 := hu (σ c) (σ c)
    have b3 := hv (σ c) (σ c)
    have b4 := hw (σ c) (σ c)
    have gc := hd c c
    grind
  rcases eq_or_ne x y with h | h
  · subst h
    exact hdiag x
  have hs : σ x ≠ σ y := fun hc ↦ h (hinj _ _ hc)
  have e1 := ht x y
  have e2 := hu x y
  have e3 := hv x y
  have e4 := hw x y
  have f1 := ht (σ x) (σ y)
  have f2 := hu (σ x) (σ y)
  have f3 := hv (σ x) (σ y)
  have f4 := hw (σ x) (σ y)
  have g := hd x y
  have dx := hdiag x
  have dy := hdiag y
  grind

/-- `x □ y = if m(X,X) = m(Y,X) then m(Y,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else if X = Y then Y
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pyx_pyx_pyy_x_y_pyy_pxx_y_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = M.op b b ∨ a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
        (fun hg2 ↦ (eq_or_ne (a) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  refine nh ?_
  have hinj : ∀ a b : G, σ a = σ b → a = b := fun a b h ↦ by
    have hh := hi1 a
    rw [h, hi1 b] at hh
    exact hh.symm
  have hdiag : ∀ c : G, σ (M.op c c) = M.op (σ c) (σ c) := fun c ↦ by
    have a1 := ht c c
    have a2 := hu c c
    have a3 := hv c c
    have a4 := hw c c
    have b1 := ht (σ c) (σ c)
    have b2 := hu (σ c) (σ c)
    have b3 := hv (σ c) (σ c)
    have b4 := hw (σ c) (σ c)
    have gc := hd c c
    grind
  rcases eq_or_ne x y with h | h
  · subst h
    exact hdiag x
  have hs : σ x ≠ σ y := fun hc ↦ h (hinj _ _ hc)
  have e1 := ht x y
  have e2 := hu x y
  have e3 := hv x y
  have e4 := hw x y
  have f1 := ht (σ x) (σ y)
  have f2 := hu (σ x) (σ y)
  have f3 := hv (σ x) (σ y)
  have f4 := hw (σ x) (σ y)
  have g := hd x y
  have dx := hdiag x
  have dy := hdiag y
  grind

/-- `x □ y = if m(X,X) = m(Y,X) then m(Y,Y) else if X = Y then X else if m(Y,X) = m(Y,Y) then m(X,X)
else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_pyx_x_y_pyx_pyy_pyy_x_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  refine nh ?_
  have hinj : ∀ a b : G, σ a = σ b → a = b := fun a b h ↦ by
    have hh := hi1 a
    rw [h, hi1 b] at hh
    exact hh.symm
  have hdiag : ∀ c : G, σ (M.op c c) = M.op (σ c) (σ c) := fun c ↦ by
    have a1 := ht c c
    have a2 := hu c c
    have a3 := hv c c
    have a4 := hw c c
    have b1 := ht (σ c) (σ c)
    have b2 := hu (σ c) (σ c)
    have b3 := hv (σ c) (σ c)
    have b4 := hw (σ c) (σ c)
    have gc := hd c c
    grind
  rcases eq_or_ne x y with h | h
  · subst h
    exact hdiag x
  have hs : σ x ≠ σ y := fun hc ↦ h (hinj _ _ hc)
  have e1 := ht x y
  have e2 := hu x y
  have e3 := hv x y
  have e4 := hw x y
  have f1 := ht (σ x) (σ y)
  have f2 := hu (σ x) (σ y)
  have f3 := hv (σ x) (σ y)
  have f4 := hw (σ x) (σ y)
  have g := hd x y
  have dx := hdiag x
  have dy := hdiag y
  grind

/-- `x □ y = if m(X,X) = X then m(X,Y) else if m(X,Y) = X then Y else if m(X,Y) = Y then X
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_x_pxy_x_pxy_y_pxy_y_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = a ∨ M.op a b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  refine nh ?_
  have hinj : ∀ a b : G, σ a = σ b → a = b := fun a b h ↦ by
    have hh := hi1 a
    rw [h, hi1 b] at hh
    exact hh.symm
  have hdiag : ∀ c : G, σ (M.op c c) = M.op (σ c) (σ c) := fun c ↦ by
    have a1 := ht c c
    have a2 := hu c c
    have a3 := hv c c
    have a4 := hw c c
    have b1 := ht (σ c) (σ c)
    have b2 := hu (σ c) (σ c)
    have b3 := hv (σ c) (σ c)
    have b4 := hw (σ c) (σ c)
    have gc := hd c c
    grind
  rcases eq_or_ne x y with h | h
  · subst h
    exact hdiag x
  have hs : σ x ≠ σ y := fun hc ↦ h (hinj _ _ hc)
  have e1 := ht x y
  have e2 := hu x y
  have e3 := hv x y
  have e4 := hw x y
  have f1 := ht (σ x) (σ y)
  have f2 := hu (σ x) (σ y)
  have f3 := hv (σ x) (σ y)
  have f4 := hw (σ x) (σ y)
  have g := hd x y
  have dx := hdiag x
  have dy := hdiag y
  grind

/-- `x □ y = if m(X,X) = X then m(X,Y) else if m(X,Y) = Y then X else if m(X,Y) = X then Y
else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut3_pxx_x_pxy_y_pxy_x_pxy_x_y_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut3_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hc4 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg3 ↦ hc3 a b hg hg2 hg3)))
  have hw : ∀ a b : G, M.op a a = a ∨ M.op a b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id
        (fun hg2 ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg3 ↦ hc4 a b hg hg2 hg3)))
  have hd := hcom
  clear hc1 hc2 hc3 hc4 hcom
  by_contra nh
  refine nh ?_
  have hinj : ∀ a b : G, σ a = σ b → a = b := fun a b h ↦ by
    have hh := hi1 a
    rw [h, hi1 b] at hh
    exact hh.symm
  have hdiag : ∀ c : G, σ (M.op c c) = M.op (σ c) (σ c) := fun c ↦ by
    have a1 := ht c c
    have a2 := hu c c
    have a3 := hv c c
    have a4 := hw c c
    have b1 := ht (σ c) (σ c)
    have b2 := hu (σ c) (σ c)
    have b3 := hv (σ c) (σ c)
    have b4 := hw (σ c) (σ c)
    have gc := hd c c
    grind
  rcases eq_or_ne x y with h | h
  · subst h
    exact hdiag x
  have hs : σ x ≠ σ y := fun hc ↦ h (hinj _ _ hc)
  have e1 := ht x y
  have e2 := hu x y
  have e3 := hv x y
  have e4 := hw x y
  have f1 := ht (σ x) (σ y)
  have f2 := hu (σ x) (σ y)
  have f3 := hv (σ x) (σ y)
  have f4 := hw (σ x) (σ y)
  have g := hd x y
  have dx := hdiag x
  have dy := hdiag y
  grind
