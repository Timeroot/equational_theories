import equational_theories.Definability.ModelCounting

/-!
# Counting inside a finite clone family

A finite injectively parametrized family containing both projections and closed
under composition can replace all operation tables in the counting obstruction.
Take the product of all source parameters. Mutual term recovery gives an
injection from these parameters to parameters satisfying the target law.
-/

open Law Law.MagmaLaw Magma

namespace Law.MagmaLaw

theorem not_termStructuralFromFin_of_cloneFamily_count
    {A P : Type} [Fintype A] [Inhabited A] [Fintype P]
    (F : P → A → A → A) (hF : Function.Injective F)
    (p₁ p₂ : P) (comp : P → P → P → P)
    (h₁ : ∀ x y, F p₁ x y = x) (h₂ : ∀ x y, F p₂ x y = y)
    (hc : ∀ p q r x y, F (comp p q r) x y = F p (F q x y) (F r x y))
    {L L' : NatMagmaLaw} (S T : P → Prop) [DecidablePred S] [DecidablePred T]
    (hS : ∀ p, S p → @satisfies _ A ⟨F p⟩ L')
    (hT : ∀ p, @satisfies _ A ⟨F p⟩ L → T p)
    (hcount : Fintype.card {p // T p} < Fintype.card {p // S p}) :
    ¬ L.TermStructuralFromFin L' := by
  classical
  intro h
  let ι := {p : P // S p}
  let op : ι → A → A → A := fun i => F i.val
  obtain ⟨N, hN, hfwd, hback⟩ := h (piMagma op) (satisfies_piMagma (fun i => hS i.val i.property))
  have hfamily : (piMagma op).IsCloneFamily
      (fun f : ι → P => piMagma (fun i => F (f i)))
      (fun _ => p₁) (fun _ => p₂) (fun f g i => comp i.val (f i) (g i)) :=
    piMagma_isCloneFamily (fun _ => h₁) (fun _ => h₂) (fun _ _ i => hc i.val _ _)
  obtain ⟨f, rfl⟩ := hfamily.exists_eq hfwd
  let image : ι → {p : P // T p} := fun i =>
    ⟨f i, hT (f i) (satisfies_of_satisfies_piMagma i hN)⟩
  have hi : Function.Injective image := by
    intro i j hij
    have he : f i = f j := congrArg Subtype.val hij
    have hn : RespectsCoordinates i j (piMagma (fun i => F (f i))).op := by
      intro x y hx hy
      change F (f i) (x i) (y i) = F (f j) (x j) (y j)
      rw [he, hx, hy]
    have hm := (respectsCoordinates_invariant hn).of_termDefinable hback
    apply Subtype.ext
    apply hF
    funext x y
    exact hm (fun _ => x) (fun _ => y) rfl rfl
  exact (not_lt_of_ge (Fintype.card_le_of_injective image hi)) hcount

end Law.MagmaLaw

/-- info: 'Law.MagmaLaw.not_termStructuralFromFin_of_cloneFamily_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Law.MagmaLaw.not_termStructuralFromFin_of_cloneFamily_count
