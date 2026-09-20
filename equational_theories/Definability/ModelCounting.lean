import equational_theories.Definability.LinearCounting

/-!
# Counting finite operation tables obstructs term recovery

Take the product of all source operations in a finite family on the same carrier.
A term-defined companion acts coordinatewise. If two coordinates acquire the
same target operation, every recovery term preserves equality between those
coordinates. The original operations must then agree. Thus distinct source
operations inject into the possible target operations.

The terms may depend on the whole product; no uniform definition across the
individual source magmas is assumed. Only small operation tables are counted.
-/

open Law Law.MagmaLaw Magma

namespace Law.MagmaLaw

theorem table_count_le_of_termStructuralFromFin
    {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
    {L L' : NatMagmaLaw} (S T : (A → A → A) → Prop)
    [DecidablePred S] [DecidablePred T]
    (hS : ∀ f, S f → @satisfies _ A ⟨f⟩ L')
    (hT : ∀ f, @satisfies _ A ⟨f⟩ L → T f)
    (h : L.TermStructuralFromFin L') :
    Fintype.card {f // S f} ≤ Fintype.card {f // T f} := by
  classical
  let ι := {f : A → A → A // S f}
  let op : ι → A → A → A := fun i => i.val
  have hs : @satisfies _ (ι → A) (piMagma op) L' :=
    satisfies_piMagma (fun i => hS i.val i.property)
  obtain ⟨N, hN, hfwd, hback⟩ := h (piMagma op) hs
  have hc : (piMagma op).IsCloneFamily
      (fun f : ι → A → A → A => piMagma f)
      (fun _ x _ => x) (fun _ _ y => y)
      (fun f g i x y => op i (f i x y) (g i x y)) :=
    piMagma_isCloneFamily (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ _ _ => rfl)
  obtain ⟨f, rfl⟩ := hc.exists_eq hfwd
  let image : ι → {g : A → A → A // T g} := fun i =>
    ⟨f i, hT (f i) (satisfies_of_satisfies_piMagma i hN)⟩
  have hi : Function.Injective image := by
    intro i j hij
    have he : f i = f j := congrArg Subtype.val hij
    have hn : RespectsCoordinates i j (piMagma f).op := by
      intro x y hx hy
      change f i (x i) (y i) = f j (x j) (y j)
      rw [he, hx, hy]
    have hm := (respectsCoordinates_invariant hn).of_termDefinable hback
    apply Subtype.ext
    funext x y
    exact hm (fun _ => x) (fun _ => y) rfl rfl
  exact Fintype.card_le_of_injective image hi

theorem not_termStructuralFromFin_of_table_count
    {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
    {L L' : NatMagmaLaw} (S T : (A → A → A) → Prop)
    [DecidablePred S] [DecidablePred T]
    (hS : ∀ f, S f → @satisfies _ A ⟨f⟩ L')
    (hT : ∀ f, @satisfies _ A ⟨f⟩ L → T f)
    (hcount : Fintype.card {f // T f} < Fintype.card {f // S f}) :
    ¬ L.TermStructuralFromFin L' := by
  intro h
  exact (not_lt_of_ge (table_count_le_of_termStructuralFromFin S T hS hT h)) hcount

end Law.MagmaLaw

/-- info: 'Law.MagmaLaw.not_termStructuralFromFin_of_table_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Law.MagmaLaw.not_termStructuralFromFin_of_table_count
