import equational_theories.Definability.Clone
import equational_theories.Definability.CloneShift

/-!
# Listed subclones, and the reverse read of term-structurality

`Definability/CloneShift.lean` refutes `TermStructuralFromFin` by trapping every clone member that
realises the target inside a *proper subclone* of the model, described by a hand-written predicate.
Writing such a predicate is algebra, and it has to be redone for every model.

This file replaces the algebra with data. A subclone can simply be **listed**: a finite family `D`
of operations containing both projections and closed under composition along any of its own
members. `Magma.InClone D` — membership in the list — is then a clone invariant of every magma
whose operation appears in the list, which is exactly the hypothesis
`Law.MagmaLaw.not_termStructuralFromFin_of_cloneInv` wants.

That makes the device mechanical. Given a finite model `M` of the source law:

* list the clone of `M` (as `Magma.IsCloneFamily` already asks for);
* for each member `⊛` of that clone, list the clone of `⊛`, which is a subclone of the first;
* a member is *irreversible* when `◇` does not appear in its own clone;
* if every clone member satisfying the target is irreversible, the cell is refuted, with `D` the
  clone of the offending member.

The listed subclones stay small — a member of a six-element clone usually generates two or three
operations — so the certificates are much cheaper than the enclosing clone. Note that no member of
the family needs to be `⊛` itself: any subclone containing `⊛` and missing `◇` will do, which is
what lets several members share one trap.

Nothing here refutes term-definability: the members really do satisfy the target, so the forward
half of term-structurality holds. What fails is the reverse half, and that is invisible to every
certificate that only looks at which operations a model can define.
-/

open Law Law.MagmaLaw

namespace Magma

variable {G : Type} {d : ℕ}

/-- `InClone D op` says that `op` is one of the operations listed by `D`. -/
def InClone (D : Fin d → Magma G) (op : G → G → G) : Prop := ∃ j, (D j).op = op

instance [DecidableEq G] [Fintype G] (D : Fin d → Magma G) (op : G → G → G) :
    Decidable (InClone D op) :=
  inferInstanceAs (Decidable (∃ _, _))

/-- `IsSubclone D` says that the listed operations contain both projections and are closed under
composition along any member of the list. Closure has to allow every member as the *outer*
operation, not just a distinguished one, because the magma whose clone invariant `InClone D`
will be is any magma in the list. -/
def IsSubclone (D : Fin d → Magma G) : Prop :=
  (∃ j, (D j).op = fun x _ ↦ x) ∧ (∃ j, (D j).op = fun _ y ↦ y) ∧
    ∀ i j l, ∃ p, (D p).op = fun x y ↦ (D i).op ((D j).op x y) ((D l).op x y)

instance [DecidableEq G] [Fintype G] (D : Fin d → Magma G) : Decidable (IsSubclone D) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- `IsSubclone` from tables: `p₁` and `p₂` name the projections and `sc i j l` names the index the
superposition of `i` over `j` and `l` lands in, so nothing has to be searched for. Deciding this
form costs `d³n²` operation lookups rather than the `d⁴n²` function comparisons the existential
costs, which is the difference between a subclone of six operations and one of thirty. -/
theorem IsSubclone.of_table {D : Fin d → Magma G} (p₁ p₂ : Fin d)
    (sc : Fin d → Fin d → Fin d → Fin d) (h₁ : ∀ x y, (D p₁).op x y = x)
    (h₂ : ∀ x y, (D p₂).op x y = y)
    (h : ∀ i j l x y, (D (sc i j l)).op x y = (D i).op ((D j).op x y) ((D l).op x y)) :
    IsSubclone D :=
  ⟨⟨p₁, funext fun x ↦ funext fun y ↦ h₁ x y⟩, ⟨p₂, funext fun x ↦ funext fun y ↦ h₂ x y⟩,
    fun i j l ↦ ⟨sc i j l, funext fun x ↦ funext fun y ↦ h i j l x y⟩⟩

/-- Failing to be in a listed subclone, pointwise: every member differs from `op` somewhere. -/
theorem notInClone_of {D : Fin d → Magma G} {op : G → G → G}
    (h : ∀ j, ¬ ∀ x y, (D j).op x y = op x y) : ¬ InClone D op :=
  fun ⟨j, hj⟩ ↦ h j fun x y ↦ by rw [hj]

/-- Membership in a listed subclone is a clone invariant of every magma in the list. -/
theorem IsSubclone.isCloneInvariant {D : Fin d → Magma G} (hD : IsSubclone D) {N : Magma G}
    (hN : InClone D N.op) : N.IsCloneInvariant (InClone D) where
  fst := hD.1
  snd := hD.2.1
  comp _ _ hf hg := by
    obtain ⟨i, hi⟩ := hN
    obtain ⟨j, hj⟩ := hf
    obtain ⟨l, hl⟩ := hg
    obtain ⟨p, hp⟩ := hD.2.2 i j l
    exact ⟨p, by rw [hp, hi, hj, hl]⟩

end Magma

namespace Law.MagmaLaw

variable {β : Type*} {L L' : Law.MagmaLaw β}

/-- Satisfaction depends on the operation, not on the packaging. -/
theorem satisfies_of_op_eq {G : Type} {M N : Magma G} (h : M.op = N.op)
    (hM : @satisfies _ G M L) : @satisfies _ G N L := by
  obtain ⟨f⟩ := M
  obtain ⟨g⟩ := N
  subst h
  exact hM

/-- **Reading a cover off the members no subclone traps.** Split the clone into the members some
subclone traps and a short list `Bad` of the rest; if none of `Bad` satisfies `L`, then every
member that does satisfy `L` is trapped.

Only the split is a statement about the whole clone, and it does not mention the target, so one
`native_decide` serves every target of the certificate. What is left per target -- that a handful
of named magmas refute it -- is an ordinary finite check on an explicit table. -/
theorem cover_of_split {G : Type} {m B : ℕ} {C : Fin m → Magma G} {Bad : Fin B → Magma G}
    {P : (G → G → G) → Prop} (hsplit : ∀ i, P (C i).op ∨ ∃ b, (C i).op = (Bad b).op)
    (hkill : ∀ b, ¬ @satisfies _ G (Bad b) L) (i : Fin m) (h : @satisfies _ G (C i) L) :
    P (C i).op :=
  (hsplit i).resolve_right fun ⟨b, hb⟩ ↦ hkill b (satisfies_of_op_eq hb h)

/-- The split of `cover_of_split`, read off witness tables: `wk i`, `we i` name the subclone and the
member matching `C i` when there is one, and `wb i` names the leftover it equals otherwise. This is
the only statement a certificate makes about its whole clone, and in this form it costs `2mn²`
lookups. -/
theorem split_of_witnesses {G : Type} {m K e B : ℕ} {C : Fin m → Magma G}
    {D : Fin K → Fin e → Magma G} {Bad : Fin B → Magma G} (wk : Fin m → Fin K)
    (we : Fin m → Fin e) (wb : Fin m → Fin B)
    (h : ∀ i, (∀ x y, (D (wk i) (we i)).op x y = (C i).op x y) ∨
      (∀ x y, (C i).op x y = (Bad (wb i)).op x y)) (i : Fin m) :
    (∃ k, Magma.InClone (D k) (C i).op) ∨ ∃ b, (C i).op = (Bad b).op :=
  (h i).imp (fun h ↦ ⟨wk i, we i, funext fun x ↦ funext fun y ↦ h x y⟩)
    fun h ↦ ⟨wb i, funext fun x ↦ funext fun y ↦ h x y⟩

/-- **The reverse read, packaged for a generator.** `M` is a finite model of `L'` whose clone is
listed by `C`; `D` is a family of listed subclones, none of which contains `M.op`; and every member
of `C` satisfying `L` lies in one of them. Then `L` is not term-structural from `L'`, even over
finite magmas.

This is `not_termStructuralFromFin_of_cloneInv` with the predicate family instantiated at
`Magma.InClone`, so that a certificate is nothing but tables of numbers. -/
theorem not_termStructuralFromFin_of_subclones {G : Type} [Finite G] [DecidableEq G] [Fintype G]
    (M : Magma G) (hM : @satisfies _ G M L') {m : ℕ} {C : Fin m → Magma G} {c : Fin m → Fin m → Fin m}
    {i₁ i₂ : Fin m} (hC : M.IsCloneFamily C i₁ i₂ c)
    {K e : ℕ} {D : Fin K → Fin e → Magma G} (hD : ∀ k, Magma.IsSubclone (D k))
    (hM0 : ∀ k, ¬ Magma.InClone (D k) M.op)
    (hL : ∀ i, @satisfies _ G (C i) L → ∃ k, Magma.InClone (D k) (C i).op) :
    ¬ L.TermStructuralFromFin L' :=
  not_termStructuralFromFin_of_cloneInv M hM hC
    (fun k _ h ↦ (hD k).isCloneInvariant h) hM0 hL

end Law.MagmaLaw
