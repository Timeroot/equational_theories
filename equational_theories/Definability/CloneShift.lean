import equational_theories.Definability.Invariant
import equational_theories.Definability.FiniteFlavour

/-!
# Shift invariants and the term-structural clone obstruction

`Definability/Clone.lean` refutes term-definability by listing the clone of a model: if no member
of the clone satisfies the target, the target is not term-definable. That certificate says nothing
about the *term-structural* relation, which is mutual — there the new operation `⊛` must also
generate `◇` back. Whenever some clone member does satisfy the target, the clone obstruction is
silent even though the cell may still be refutable, because every such member may fail to generate.

This file supplies the missing device. Instead of asking for a member satisfying the target we ask
for a member that satisfies the target *and* generates `◇`; the second half is refuted by exhibiting
a **proper subclone** containing it. A subclone is described by a predicate `P` that is a
`Magma.IsCloneInvariant` of the candidate operation itself: then everything term-definable from `⊛`
satisfies `P`, so if `◇` does not satisfy `P`, then `◇` is not term-definable from `⊛`.

`Law.MagmaLaw.not_termStructuralFromFin_of_cloneInv` packages this. It takes a *family* of such
predicates, indexed by `κ`, because a single subclone rarely covers every clone member satisfying
the target; each member is handed the predicate that traps it.

The rest of the file provides the predicates themselves for a permutation `s` of order dividing
three. All three are stated for an arbitrary `s` and an arbitrary carrier, and all three are
`IsCloneInvariant` of any operation satisfying them, so they are reusable certificates rather than
one-off algebra:

* `Magma.SplitShift s u` — `u` is `s`-blind in one argument and `s`-equivariant in the other;
* `Magma.RespShift s u` — shifting an argument by `s` moves the value inside its own `⟨s⟩`-orbit;
* `Magma.DiagShift s u` — `RespShift`, and the diagonal `u x x` stays in the orbit of `x`.

On the order-nine models of equation 692 these three, at two different translations `s`, cut out
exactly the three maximal proper subclones.
-/

open FirstOrder Law Law.MagmaLaw

namespace Magma

variable {G : Type}

/-! ### Orbits of a permutation of order three -/

/-- `Orb3 s z z'` says that `z'` lies in the `⟨s⟩`-orbit of `z`, for an `s` with `s³ = id`. -/
def Orb3 (s : G → G) (z z' : G) : Prop := z' = z ∨ z' = s z ∨ z' = s (s z)

instance [DecidableEq G] (s : G → G) (z z' : G) : Decidable (Orb3 s z z') :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

theorem Orb3.refl {s : G → G} (z : G) : Orb3 s z z := Or.inl rfl

theorem Orb3.step {s : G → G} (z : G) : Orb3 s z (s z) := Or.inr (Or.inl rfl)

theorem Orb3.trans {s : G → G} {a b c : G} (h₁ : Orb3 s a b) (h₂ : Orb3 s b c)
    (hs : ∀ x, s (s (s x)) = x) : Orb3 s a c := by
  unfold Orb3 at h₁ h₂ ⊢
  rcases h₁ with rfl | rfl | rfl <;> rcases h₂ with rfl | rfl | rfl <;>
    simp only [hs] <;> tauto

/-! ### `RespShift`: shifting an argument stays inside the orbit -/

/-- `RespShift s u` says that shifting either argument of `u` by `s` moves the value inside its own
`⟨s⟩`-orbit. -/
def RespShift (s : G → G) (u : G → G → G) : Prop :=
  (∀ x y, Orb3 s (u x y) (u (s x) y)) ∧ (∀ x y, Orb3 s (u x y) (u x (s y)))

instance [DecidableEq G] [Fintype G] (s : G → G) (u : G → G → G) :
    Decidable (RespShift s u) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Moving the first argument of a `RespShift` operation inside an orbit keeps the value inside an
orbit. -/
theorem RespShift.left {s : G → G} {u : G → G → G} (hu : RespShift s u)
    (hs : ∀ x, s (s (s x)) = x) {p p' : G} (h : Orb3 s p p') (q : G) :
    Orb3 s (u p q) (u p' q) := by
  unfold Orb3 at h
  rcases h with rfl | rfl | rfl
  · exact Orb3.refl _
  · exact hu.1 p q
  · exact (hu.1 p q).trans (hu.1 (s p) q) hs

/-- Moving the second argument of a `RespShift` operation inside an orbit keeps the value inside an
orbit. -/
theorem RespShift.right {s : G → G} {u : G → G → G} (hu : RespShift s u)
    (hs : ∀ x, s (s (s x)) = x) (p : G) {q q' : G} (h : Orb3 s q q') :
    Orb3 s (u p q) (u p q') := by
  unfold Orb3 at h
  rcases h with rfl | rfl | rfl
  · exact Orb3.refl _
  · exact hu.2 p q
  · exact (hu.2 p q).trans (hu.2 p (s q)) hs

/-- The operations respecting the orbits of `s` form a subclone of any magma whose own operation
respects them. -/
theorem RespShift.isCloneInvariant {s : G → G} (hs : ∀ x, s (s (s x)) = x) {N : Magma G}
    (hN : RespShift s N.op) : N.IsCloneInvariant (RespShift s) where
  fst := ⟨fun x _ ↦ Orb3.step x, fun x _ ↦ Orb3.refl x⟩
  snd := ⟨fun _ y ↦ Orb3.refl y, fun _ y ↦ Orb3.step y⟩
  comp _ g hf hg :=
    ⟨fun x y ↦ (hN.left hs (hf.1 x y) (g x y)).trans (hN.right hs _ (hg.1 x y)) hs,
     fun x y ↦ (hN.left hs (hf.2 x y) (g x y)).trans (hN.right hs _ (hg.2 x y)) hs⟩

/-! ### `DiagShift`: the diagonal stays in the orbit of its argument -/

/-- `DiagShift s u` is `RespShift s u` together with `u x x` lying in the `⟨s⟩`-orbit of `x`. -/
def DiagShift (s : G → G) (u : G → G → G) : Prop :=
  RespShift s u ∧ ∀ x, Orb3 s x (u x x)

instance [DecidableEq G] [Fintype G] (s : G → G) (u : G → G → G) :
    Decidable (DiagShift s u) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The operations with orbit-bounded diagonal form a subclone of any magma whose own operation has
one. -/
theorem DiagShift.isCloneInvariant {s : G → G} (hs : ∀ x, s (s (s x)) = x) {N : Magma G}
    (hN : DiagShift s N.op) : N.IsCloneInvariant (DiagShift s) where
  fst := ⟨(RespShift.isCloneInvariant hs hN.1).fst, fun x ↦ Orb3.refl x⟩
  snd := ⟨(RespShift.isCloneInvariant hs hN.1).snd, fun x ↦ Orb3.refl x⟩
  comp f g hf hg :=
    ⟨(RespShift.isCloneInvariant hs hN.1).comp f g hf.1 hg.1,
     fun x ↦ ((hN.2 x).trans (hN.1.left hs (hf.2 x) x) hs).trans
       (hN.1.right hs _ (hg.2 x)) hs⟩

/-! ### `SplitShift`: one argument is blind to `s`, the other equivariant -/

/-- `ShiftKind s u b` says that `u` is `s`-blind in one argument and `s`-equivariant in the other;
`b = true` names the second argument as the equivariant one. -/
def ShiftKind (s : G → G) (u : G → G → G) : Bool → Prop
  | true => (∀ x y, u (s x) y = u x y) ∧ (∀ x y, u x (s y) = s (u x y))
  | false => (∀ x y, u (s x) y = s (u x y)) ∧ (∀ x y, u x (s y) = u x y)

instance [DecidableEq G] [Fintype G] (s : G → G) (u : G → G → G) :
    ∀ b, Decidable (ShiftKind s u b)
  | true => inferInstanceAs (Decidable (_ ∧ _))
  | false => inferInstanceAs (Decidable (_ ∧ _))

/-- `SplitShift s u` says that one argument of `u` is blind to `s` and the other is `s`-equivariant.
Which is which is not fixed: the two projections take opposite sides. -/
def SplitShift (s : G → G) (u : G → G → G) : Prop := ∃ b, ShiftKind s u b

instance [DecidableEq G] [Fintype G] (s : G → G) (u : G → G → G) :
    Decidable (SplitShift s u) :=
  inferInstanceAs (Decidable (∃ _, _))

/-- Composing along an operation of kind `bw` produces an operation whose kind is that of the
argument sitting in `w`'s equivariant slot: the outer operation is blind to whatever the other
argument does. -/
theorem ShiftKind.comp {s : G → G} {w f g : G → G → G} {bw bf bg : Bool}
    (hw : ShiftKind s w bw) (hf : ShiftKind s f bf) (hg : ShiftKind s g bg) :
    ShiftKind s (fun x y ↦ w (f x y) (g x y)) (bif bw then bg else bf) := by
  cases bw <;> cases bf <;> cases bg <;>
    simp only [ShiftKind, cond_true, cond_false] at hw hf hg ⊢ <;>
    exact ⟨fun x y ↦ by simp only [hf, hg, hw], fun x y ↦ by simp only [hf, hg, hw]⟩

/-- The split operations form a subclone of any magma whose own operation is split. -/
theorem SplitShift.isCloneInvariant {s : G → G} {N : Magma G} (hN : SplitShift s N.op) :
    N.IsCloneInvariant (SplitShift s) where
  fst := ⟨false, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  snd := ⟨true, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  comp _ _ hf hg :=
    let ⟨_, hw⟩ := hN
    let ⟨_, hf⟩ := hf
    let ⟨_, hg⟩ := hg
    ⟨_, hw.comp hf hg⟩

end Magma

namespace Law.MagmaLaw

variable {β : Type*} {L L' : Law.MagmaLaw β}

/-- **Term-structural clone obstruction.** Let `M` be a finite model of `L'` whose clone is listed
by the family `C`. Suppose `Q` is a family of predicates such that

* each `Q k` is a clone invariant of every magma whose operation satisfies it (`hQ`);
* `M.op` itself satisfies none of them (`hM0`);
* every member of the clone satisfying `L` satisfies some `Q k` (`hL`).

Then `L` is not term-structural from `L'`, even over finite magmas. Indeed a witness `⊛` would be
some `C i` satisfying `L`, hence trapped by some `Q k`; but `Q k` is then a clone invariant of `⊛`,
so `◇ = M.op` — being term-definable from `⊛` — would have to satisfy it too, contradicting `hM0`.

This is the mutual counterpart of `not_termDefinableFrom_of_clone`, which can only fire when *no*
clone member satisfies `L`. Here members may satisfy `L` freely; what they may not do is generate
`◇` back. -/
theorem not_termStructuralFromFin_of_cloneInv {G : Type} [Finite G] (M : Magma G)
    (hM : @satisfies _ G M L') {ι : Type*} {C : ι → Magma G} {i₁ i₂ : ι} {c : ι → ι → ι}
    (hC : M.IsCloneFamily C i₁ i₂ c) {κ : Type*} {Q : κ → (G → G → G) → Prop}
    (hQ : ∀ (k : κ) (N : Magma G), Q k N.op → N.IsCloneInvariant (Q k))
    (hM0 : ∀ k, ¬ Q k M.op)
    (hL : ∀ i, @satisfies _ G (C i) L → ∃ k, Q k (C i).op) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  obtain ⟨M', hM', hfwd, hback⟩ := h M hM
  obtain ⟨i, hi⟩ := hC.exists_eq hfwd
  subst hi
  obtain ⟨k, hk⟩ := hL i hM'
  exact hM0 k ((hQ k _ hk).of_termDefinable hback)

/-- The unrestricted form of `not_termStructuralFromFin_of_cloneInv`; the finite form is stronger. -/
theorem not_termStructuralFrom_of_cloneInv {G : Type} [Finite G] (M : Magma G)
    (hM : @satisfies _ G M L') {ι : Type*} {C : ι → Magma G} {i₁ i₂ : ι} {c : ι → ι → ι}
    (hC : M.IsCloneFamily C i₁ i₂ c) {κ : Type*} {Q : κ → (G → G → G) → Prop}
    (hQ : ∀ (k : κ) (N : Magma G), Q k N.op → N.IsCloneInvariant (Q k))
    (hM0 : ∀ k, ¬ Q k M.op)
    (hL : ∀ i, @satisfies _ G (C i) L → ∃ k, Q k (C i).op) :
    ¬ L.TermStructuralFrom L' := fun h ↦
  not_termStructuralFromFin_of_cloneInv M hM hC hQ hM0 hL (termStructuralFin_of_termStructural h)

end Law.MagmaLaw
