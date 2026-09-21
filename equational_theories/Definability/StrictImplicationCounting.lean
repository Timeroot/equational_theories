import equational_theories.Definability.ModelCounting

/-!
A proper inclusion of finite model classes cannot be reversed by term-structural
definitions. The product of all source operations on a fixed finite carrier would
give an injection into the target operations. An ordinary implication supplies
the opposite inclusion, and one counterexample makes that inclusion strict.
No enumeration or numerical evaluation of either model count is needed.
-/

namespace Law.MagmaLaw

theorem not_termStructuralFromFin_of_strict_implication
    {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
    {L L' : NatMagmaLaw} (himp : L.implies L')
    (M : Magma A) (hsource : @satisfies _ A M L')
    (htarget : ¬ @satisfies _ A M L) :
    ¬ L.TermStructuralFromFin L' := by
  classical
  let S (f : A → A → A) := @satisfies _ A ⟨f⟩ L'
  let T (f : A → A → A) := @satisfies _ A ⟨f⟩ L
  apply not_termStructuralFromFin_of_table_count S T
    (fun _ h => h) (fun _ h => h)
  let inclusion : {f // T f} → {f // S f} :=
    fun f => ⟨f.val, @himp A ⟨f.val⟩ f.property⟩
  have hi : Function.Injective inclusion := by
    intro f g h
    exact Subtype.ext (congrArg (fun p : {f // S f} => p.val) h)
  apply Fintype.card_lt_of_injective_of_notMem inclusion hi (b := ⟨M.op, hsource⟩)
  rintro ⟨f, hf⟩
  apply htarget
  have he : f.val = M.op := congrArg Subtype.val hf
  simpa only [T, he] using f.property

end Law.MagmaLaw

/-- info: 'Law.MagmaLaw.not_termStructuralFromFin_of_strict_implication' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Law.MagmaLaw.not_termStructuralFromFin_of_strict_implication
