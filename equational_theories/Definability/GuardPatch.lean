import equational_theories.Definability.CommPatch

/-!
# Commutative patches from an asymmetric word and a symmetrising guard

`Definability/CommPatch.lean` buys the whole commutative-idempotent rectangle of targets from a
single fact about the source: that it proves some word `w(x, y)` symmetric. That is a strong
demand, and for most of the sources still open in that rectangle the banked finite models refute
every word outright.

But symmetry of `w` is more than the patch actually needs. Take

    x □ y  :=  if x = y then x else if a(x, y) = b(x, y) then w(x, y) else w(y, x)

which is still a decision tree over term equations, hence still `QFOp` and still definable for
free. Write `G(x, y)` for the guard `a(x, y) = b(x, y)`. Off the diagonal there are four cases,
and in two of them commutativity is automatic:

    G(x, y),  ¬G(y, x)  ->  x □ y = w(x, y),  y □ x = w(x, y)   -- agree, whatever `w` is
    ¬G(x, y),  G(y, x)  ->  x □ y = w(y, x),  y □ x = w(y, x)   -- likewise

The guard has *oriented* the pair, and the operation reads `w` the same way round from both sides.
Only when the guard cannot tell `(x, y)` from `(y, x)` -- when `G(x, y) ↔ G(y, x)` -- does the
burden fall back on `w`. So the hypothesis is not "`w` is symmetric" but the strictly weaker

    G(x, y) ↔ G(y, x)   ->   w(x, y) = w(y, x)

and a symmetric `w` is the degenerate case where the guard is never consulted. `symmTerm`'s
sources are exactly the `guardedSymm` sources with `a = b`.
-/

open FirstOrder FirstOrder.Language Law Law.MagmaLaw

variable {G : Type}

namespace QFOp

open FreeMagma

/-- A word with its two arguments exchanged. -/
def swapArgs (w : FreeMagma (Fin 2)) : FreeMagma (Fin 2) := fmapHom ![1, 0] w

private theorem comp_swap {G : Type} (x y : G) : (![x, y] ∘ ![(1 : Fin 2), 0]) = ![y, x] := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

theorem eval_swapArgs (M : Magma G) (w : FreeMagma (Fin 2)) (x y : G) :
    @evalInMagma _ _ M ![x, y] (swapArgs w) = @evalInMagma _ _ M ![y, x] w := by
  rw [swapArgs, @evalInMagma_fmapHom, comp_swap]

/-- `x □ y := if x = y then x else if a(x, y) = b(x, y) then w(x, y) else w(y, x)`. -/
def gpatch (a b w : FreeMagma (Fin 2)) : QFOp :=
  .ite (Lf 0) (Lf 1) (.leaf (Lf 0)) (.ite a b (.leaf w) (.leaf (swapArgs w)))

open scoped Classical in
theorem gpatch_apply (M : Magma G) (a b w : FreeMagma (Fin 2)) (x y : G) :
    ((gpatch a b w).magma M).op x y =
      if x = y then x else
        if @evalInMagma _ _ M ![x, y] a = @evalInMagma _ _ M ![x, y] b then
          @evalInMagma _ _ M ![x, y] w
        else @evalInMagma _ _ M ![y, x] w := by
  show @eval _ M (gpatch a b w) ![x, y] = _
  simp only [gpatch, eval, evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one,
    eval_swapArgs M w x y]

theorem gpatch_diag (M : Magma G) (a b w : FreeMagma (Fin 2)) (x : G) :
    ((gpatch a b w).magma M).op x x = x := by
  classical
  rw [gpatch_apply]
  simp

/-- The guard orients every pair it can distinguish, and `w` only has to be symmetric on the
pairs left over. -/
theorem gpatch_comm (M : Magma G) (a b w : FreeMagma (Fin 2))
    (hw : ∀ x y : G,
      ((@evalInMagma _ _ M ![x, y] a = @evalInMagma _ _ M ![x, y] b) ↔
        (@evalInMagma _ _ M ![y, x] a = @evalInMagma _ _ M ![y, x] b)) →
      @evalInMagma _ _ M ![x, y] w = @evalInMagma _ _ M ![y, x] w) (x y : G) :
    ((gpatch a b w).magma M).op x y = ((gpatch a b w).magma M).op y x := by
  classical
  rcases eq_or_ne x y with rfl | hxy
  · rfl
  rw [gpatch_apply, gpatch_apply, if_neg hxy, if_neg hxy.symm]
  by_cases h₁ : @evalInMagma _ _ M ![x, y] a = @evalInMagma _ _ M ![x, y] b <;>
    by_cases h₂ : @evalInMagma _ _ M ![y, x] a = @evalInMagma _ _ M ![y, x] b
  · rw [if_pos h₁, if_pos h₂]
    exact hw x y ⟨fun _ ↦ h₂, fun _ ↦ h₁⟩
  · rw [if_pos h₁, if_neg h₂]
  · rw [if_neg h₁, if_pos h₂]
  · rw [if_neg h₁, if_neg h₂]
    exact hw y x ⟨fun h ↦ absurd h h₂, fun h ↦ absurd h h₁⟩

end QFOp

namespace Law.MagmaLaw

open QFOp FreeMagma

variable {β : Type*} {L L' : Law.MagmaLaw β}

/-- Glue, in the shape the sweep produces it: a guard `a = b` and a word `w`, together with the
source's proof that the guard symmetrises the word. -/
theorem definableFrom_of_guardedSymm (a b w : FreeMagma (Fin 2))
    (hw : ∀ {G : Type} (M : Magma G), satisfies G L' → ∀ x y : G,
      ((@evalInMagma _ _ M ![x, y] a = @evalInMagma _ _ M ![x, y] b) ↔
        (@evalInMagma _ _ M ![y, x] a = @evalInMagma _ _ M ![y, x] b)) →
      @evalInMagma _ _ M ![x, y] w = @evalInMagma _ _ M ![y, x] w)
    (hL : ∀ {G : Type} (N : Magma G), (∀ x : G, N.op x x = x) →
      (∀ x y : G, N.op x y = N.op y x) → @satisfies _ G N L) :
    L.DefinableFrom L' :=
  definableFrom_of_qfOp (gpatch a b w) fun M hM ↦
    hL ((gpatch a b w).magma M) (gpatch_diag M a b w) (gpatch_comm M a b w (hw M hM))

/-! ### The two comm+idem targets `CommPatch` did not bundle -/

theorem commIdem_43 {G : Type} (N : Magma G) (_ : ∀ x : G, N.op x x = x)
    (hc : ∀ x y : G, N.op x y = N.op y x) : @satisfies _ G N Law43 := by
  rw [@Law43.models_iff G N]
  exact hc

theorem commIdem_4405 {G : Type} (N : Magma G) (_ : ∀ x : G, N.op x x = x)
    (hc : ∀ x y : G, N.op x y = N.op y x) : @satisfies _ G N Law4405 := by
  rw [@Law4405.models_iff G N]
  intro x y
  rw [hc y x, hc (N.op x y) x, hc x y]

end Law.MagmaLaw
