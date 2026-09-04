import equational_theories.Definability.Invariant
import equational_theories.Definability.FiniteFlavour

/-!
# Three universal clone invariants, and the invariant form of the term-structural obstruction

`Definability/CloneShift.lean` refutes the term-structural relation by trapping every clone member
that realises the target inside a *proper subclone*, so that none of them can generate `◇` back.
The subclones there are cut out by shift invariants, which are tailored to a permutation of order
three. This file supplies three subclone predicates that need no tailoring at all — they are clone
invariants of *any* magma whose operation satisfies them, on *any* carrier:

* `Magma.DiagFixed u` — `u` is idempotent, `u x x = x`;
* `Magma.IgnoreArg u` — `u` ignores one of its two arguments;
* `Magma.Equivariant σ u` — the fixed map `σ` is an endomorphism of `u`.

Each is a one-line induction: composing idempotent operations along an idempotent one is
idempotent; composing along an operation that ignores an argument passes the dependence through to
whichever argument survives; and a map that is an endomorphism of `◇` is an endomorphism of every
term of `◇`. Together they are surprisingly strong. On the linear models of a linear law they cut
out, respectively, the operations of weight one, the degenerate ones, and the ones whose
coefficients lie in a subfield — which is often the whole set of non-generators.

The file also carries `Law.MagmaLaw.not_termStructuralFromFin_of_invariant`, the predicate form of
`not_termStructuralFromFin_of_cloneInv`: the clone of the model is described by a
`Magma.IsCloneInvariant` rather than by a listed family, which for an algebraically described clone
avoids emitting a composition table entirely.
-/

open FirstOrder Law Law.MagmaLaw

namespace Magma

variable {G : Type}

/-! ### `DiagFixed`: idempotence -/

/-- `DiagFixed u` says that `u` is idempotent. -/
def DiagFixed (u : G → G → G) : Prop := ∀ x, u x x = x

instance [DecidableEq G] [Fintype G] (u : G → G → G) : Decidable (DiagFixed u) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- The idempotent operations form a subclone of any idempotent magma. -/
theorem DiagFixed.isCloneInvariant {N : Magma G} (hN : DiagFixed N.op) :
    N.IsCloneInvariant DiagFixed where
  fst _ := rfl
  snd _ := rfl
  comp f g hf hg x := by
    show N.op (f x x) (g x x) = x
    rw [hf x, hg x]
    exact hN x

/-! ### `IgnoreArg`: degeneracy -/

/-- `IgnoreKind u b` says that `u` ignores its first argument (`b = true`) or its second
(`b = false`). -/
def IgnoreKind (u : G → G → G) : Bool → Prop
  | false => ∀ x y y', u x y = u x y'
  | true => ∀ x x' y, u x y = u x' y

instance [DecidableEq G] [Fintype G] (u : G → G → G) : ∀ b, Decidable (IgnoreKind u b)
  | false => inferInstanceAs (Decidable (∀ _, _))
  | true => inferInstanceAs (Decidable (∀ _, _))

/-- `IgnoreArg u` says that `u` ignores one of its two arguments. -/
def IgnoreArg (u : G → G → G) : Prop := ∃ b, IgnoreKind u b

instance [DecidableEq G] [Fintype G] (u : G → G → G) : Decidable (IgnoreArg u) :=
  inferInstanceAs (Decidable (∃ _, _))

/-- Composing along an operation that ignores an argument produces an operation that ignores
whichever argument the surviving input ignores. -/
theorem IgnoreKind.comp {w f g : G → G → G} {bw bf bg : Bool}
    (hw : IgnoreKind w bw) (hf : IgnoreKind f bf) (hg : IgnoreKind g bg) :
    IgnoreKind (fun x y ↦ w (f x y) (g x y)) (bif bw then bg else bf) := by
  cases bw
  · cases bf
    · exact fun x y y' ↦ show w (f x y) (g x y) = w (f x y') (g x y') by
        rw [hf x y y']; exact hw _ _ _
    · exact fun x x' y ↦ show w (f x y) (g x y) = w (f x' y) (g x' y) by
        rw [hf x x' y]; exact hw _ _ _
  · cases bg
    · exact fun x y y' ↦ show w (f x y) (g x y) = w (f x y') (g x y') by
        rw [hg x y y']; exact hw _ _ _
    · exact fun x x' y ↦ show w (f x y) (g x y) = w (f x' y) (g x' y) by
        rw [hg x x' y]; exact hw _ _ _

/-- The degenerate operations form a subclone of any degenerate magma. -/
theorem IgnoreArg.isCloneInvariant {N : Magma G} (hN : IgnoreArg N.op) :
    N.IsCloneInvariant IgnoreArg where
  fst := ⟨false, fun _ _ _ ↦ rfl⟩
  snd := ⟨true, fun _ _ _ ↦ rfl⟩
  comp _ _ hf hg :=
    let ⟨_, hw⟩ := hN
    let ⟨_, hf⟩ := hf
    let ⟨_, hg⟩ := hg
    ⟨_, hw.comp hf hg⟩

/-! ### `Equivariant`: an endomorphism of the operation -/

/-- `Equivariant σ u` says that the fixed map `σ` is an endomorphism of `u`. -/
def Equivariant (σ : G → G) (u : G → G → G) : Prop := ∀ x y, u (σ x) (σ y) = σ (u x y)

instance [DecidableEq G] [Fintype G] (σ : G → G) (u : G → G → G) :
    Decidable (Equivariant σ u) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- The operations admitting `σ` as an endomorphism form a subclone of any magma admitting it. -/
theorem Equivariant.isCloneInvariant {σ : G → G} {N : Magma G} (hN : Equivariant σ N.op) :
    N.IsCloneInvariant (Equivariant σ) where
  fst _ _ := rfl
  snd _ _ := rfl
  comp f g hf hg x y := by
    show N.op (f (σ x) (σ y)) (g (σ x) (σ y)) = σ (N.op (f x y) (g x y))
    rw [hf x y, hg x y]
    exact hN _ _

end Magma

namespace Law.MagmaLaw

variable {β : Type*} {L L' : Law.MagmaLaw β}

/-- **Invariant clone obstruction, finite flavour.** `not_termDefinableFrom_of_invariant` with the
model required to be finite and the conclusion strengthened accordingly: refuting
`TermDefinableFromFin` refutes `TermDefinableFrom` as well, by `termDefinableFin_of_termDefinable`.

This is to `not_termDefinableFromFin_of_clone` exactly what `not_termDefinableFrom_of_invariant` is
to `not_termDefinableFrom_of_clone` — the clone described by a predicate instead of a list, which
is what a carrier of eighty-one elements needs. -/
theorem not_termDefinableFromFin_of_invariant {G : Type} [Finite G] (M : Magma G)
    (hM : @satisfies _ G M L') {P : (G → G → G) → Prop} (hP : M.IsCloneInvariant P)
    (hL : ∀ op, P op → ¬ @satisfies _ G (Magma.mk op) L) :
    ¬ L.TermDefinableFromFin L' := fun h ↦
  let ⟨M', hM', hd⟩ := h M hM
  hL M'.op (hP.of_termDefinable hd) hM'

/-- **Term-structural obstruction, invariant form.** Let `M` be a finite model of `L'` and `P` a
clone invariant of `M` — a predicate that holds of everything term-definable from `M`. Suppose `Q`
is a family of predicates such that

* each `Q k` is a clone invariant of every magma whose operation satisfies it (`hQ`);
* `M.op` itself satisfies none of them (`hM0`);
* every operation satisfying `P` and realising `L` satisfies some `Q k` (`hL`).

Then `L` is not term-structural from `L'`, even over finite magmas.

This is `not_termStructuralFromFin_of_cloneInv` with the listed clone family replaced by a
predicate, exactly as `not_termDefinableFrom_of_invariant` is the predicate form of
`not_termDefinableFrom_of_clone`. When the clone is described algebraically — "all linear maps over
this field", say — the predicate form needs no composition table. -/
theorem not_termStructuralFromFin_of_invariant {G : Type} [Finite G] (M : Magma G)
    (hM : @satisfies _ G M L') {P : (G → G → G) → Prop} (hP : M.IsCloneInvariant P)
    {κ : Type*} {Q : κ → (G → G → G) → Prop}
    (hQ : ∀ (k : κ) (N : Magma G), Q k N.op → N.IsCloneInvariant (Q k))
    (hM0 : ∀ k, ¬ Q k M.op)
    (hL : ∀ op : G → G → G, P op → @satisfies _ G (Magma.mk op) L → ∃ k, Q k op) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h M hM
  obtain ⟨op⟩ := M'
  obtain ⟨k, hk⟩ := hL op (hP.of_termDefinable hfwd) hM'
  exact hM0 k ((hQ k (Magma.mk op) hk).of_termDefinable hback)

/-- The unrestricted form of `not_termStructuralFromFin_of_invariant`; the finite form is
stronger. -/
theorem not_termStructuralFrom_of_invariant {G : Type} [Finite G] (M : Magma G)
    (hM : @satisfies _ G M L') {P : (G → G → G) → Prop} (hP : M.IsCloneInvariant P)
    {κ : Type*} {Q : κ → (G → G → G) → Prop}
    (hQ : ∀ (k : κ) (N : Magma G), Q k N.op → N.IsCloneInvariant (Q k))
    (hM0 : ∀ k, ¬ Q k M.op)
    (hL : ∀ op : G → G → G, P op → @satisfies _ G (Magma.mk op) L → ∃ k, Q k op) :
    ¬ L.TermStructuralFrom L' := fun h ↦
  not_termStructuralFromFin_of_invariant M hM hP hQ hM0 hL (termStructuralFin_of_termStructural h)

end Law.MagmaLaw
