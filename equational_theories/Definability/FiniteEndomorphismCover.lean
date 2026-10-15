import equational_theories.Definability.UnaryMapCounting

/-! A finite source list and a complete, shorter target list suffice for the
clone-count obstruction. The commuting operation family itself is never
enumerated by Lean. In particular the prescribed unary map may have tails. -/

open Law Law.MagmaLaw

namespace Magma.UnaryMap

theorem not_termStructuralFromFin_of_cover
    {A S T : Type} [Fintype A] [Inhabited A] [Fintype S] [Fintype T]
    (u : A → A) (sources : S → A → A → A) (targets : T → A → A → A)
    (hinj : Function.Injective sources)
    {L L' : NatMagmaLaw}
    (hs : ∀ i, @satisfies _ A ⟨sources i⟩ L')
    (hu : ∀ i, Commutes u (sources i))
    (hcover : ∀ f, Commutes u f → @satisfies _ A ⟨f⟩ L → ∃ j, targets j = f)
    (hsize : Fintype.card T < Fintype.card S) :
    ¬ L.TermStructuralFromFin L' := by
  classical
  let IsSource (p : P u) : Prop := ∃ i, sources i = p.val
  let IsTarget (p : P u) : Prop := @satisfies _ A ⟨p.val⟩ L
  apply not_termStructuralFromFin_of_cloneFamily_count (@op A u) (op_injective u)
    (fst u) (snd u) comp (op_fst u) (op_snd u) op_comp IsSource IsTarget
  · rintro p ⟨i, hi⟩
    change @satisfies _ A ⟨p.val⟩ L'
    rw [← hi]
    exact hs i
  · intro p hp
    exact hp
  · let sourceIndex : S → {p : P u // IsSource p} :=
      fun i => ⟨⟨sources i, hu i⟩, i, rfl⟩
    have hsource : Function.Injective sourceIndex := by
      intro i j hij
      exact hinj (congrArg (fun p => p.val.val) hij)
    have ht : ∀ p : {p : P u // IsTarget p}, ∃ j, targets j = p.val.val :=
      fun p => hcover _ p.val.property p.property
    choose targetIndex htarget using ht
    have htarget_inj : Function.Injective targetIndex := by
      intro p q hpq
      apply Subtype.ext
      apply Subtype.ext
      exact (htarget p).symm.trans ((congrArg targets hpq).trans (htarget q))
    exact lt_of_le_of_lt (Fintype.card_le_of_injective targetIndex htarget_inj)
      (lt_of_lt_of_le hsize (Fintype.card_le_of_injective sourceIndex hsource))

end Magma.UnaryMap

/-- info: 'Magma.UnaryMap.not_termStructuralFromFin_of_cover' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.UnaryMap.not_termStructuralFromFin_of_cover
