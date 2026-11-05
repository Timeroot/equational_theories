import equational_theories.Parastrophes.Equation917SplitCandidate
import equational_theories.Parastrophes.Equation917FrontProduct
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.GroupAction.Quotient
/-!
# Mixed-word constraints for E917 candidate searches

A left-index/output autotopy satisfies g(x)*y=f(x*y). Two such pairs whose
outputs agree at one point agree everywhere: use the row through that point
to compare the input maps, then reparameterize the same row to compare all
output values. Composition preserves autotopies. Consequently every relation
between mixed words in the normalized FrontProduct outputs a,b holds globally
as soon as it holds at one point. This is stronger search pruning than only
requiring the individual permutations to have uniform cycle lengths.

No commutativity or restriction on the generated group's order is assumed.
-/
namespace Parastrophes.Eq917Image.SplitCandidate
variable {A : Type} (D : Magma A)

/-- Two left-index/output autotopies agreeing at one output point agree
at every point. The maps need not be assumed bijective. -/
theorem output_agreement (g f g' f' : A → A) (hq : IsQuasigroup D)
    (h : ∀ x y, D.op (g x) y=f (D.op x y))
    (h' : ∀ x y, D.op (g' x) y=f' (D.op x y))
    (o : A) (ho : f o=f' o) : (∀ x, g x=g' x) ∧ (∀ x, f x=f' x) := by
  obtain ⟨y,hy⟩ := (hq.1 o).2 o
  have go : g o=g' o := by
    apply (hq.2 y).1
    change D.op (g o) y=D.op (g' o) y
    rw [h,h',hy,ho]
  have ff (x) : f x=f' x := by
    obtain ⟨z,rfl⟩ := (hq.1 o).2 x
    rw [← h,← h',go]
  refine ⟨?_,ff⟩
  intro x
  apply (hq.2 o).1
  exact (h x o).trans ((ff _).trans (h' x o).symm)

/-- Evaluation of a word in two maps, with the first letter outermost. -/
def word (f g : A → A) : List Bool → A → A
  | [], x => x
  | false::w,x => f (word f g w x)
  | true::w,x => g (word f g w x)

theorem word_autotopy (g f g' f' : A → A)
    (h : ∀ x y, D.op (g x) y=f (D.op x y))
    (h' : ∀ x y, D.op (g' x) y=f' (D.op x y))
    (w : List Bool) (x y : A) :
    D.op (word g g' w x) y=word f f' w (D.op x y) := by
  induction w with
  | nil => rfl
  | cons c w ih => cases c <;> simp only [word,h,h',ih]

/-- Every relation between mixed words in the output maps propagates from
one point to the whole carrier. This strengthens separate cycle pruning. -/
theorem word_output_agreement (g f g' f' : A → A) (hq : IsQuasigroup D)
    (h : ∀ x y, D.op (g x) y=f (D.op x y))
    (h' : ∀ x y, D.op (g' x) y=f' (D.op x y))
    (w v : List Bool) (o : A) (ho : word f f' w o=word f f' v o) :
    ∀ x, word f f' w x=word f f' v x :=
  (output_agreement D _ _ _ _ hq (word_autotopy D g f g' f' h h' w)
    (word_autotopy D g f g' f' h h' v) o ho).2
/-- Permutations that occur on the output side of a left-index autotopy. -/
def outputGroup : Subgroup (Equiv.Perm A) where
  carrier := {f | ∃ g : Equiv.Perm A, ∀ x y, D.op (g x) y=f (D.op x y)}
  one_mem' := ⟨1,fun _ _ => rfl⟩
  mul_mem' := by
    rintro f f' ⟨g,hg⟩ ⟨g',hg'⟩
    refine ⟨g*g',?_⟩
    intro x y
    change D.op (g (g' x)) y=f (f' (D.op x y))
    rw [hg,hg']
  inv_mem' := by
    rintro f ⟨g,hg⟩
    refine ⟨g⁻¹,?_⟩
    intro x y
    apply f.injective
    change f (D.op (g.symm x) y)=f (f.symm (D.op x y))
    rw [← hg,g.apply_symm_apply,f.apply_symm_apply]

/-- Its action is free, so evaluating at one point faithfully embeds the
entire group into the carrier. -/
theorem outputGroup_eval_injective (hq : IsQuasigroup D) (o : A) :
    Function.Injective (fun f : outputGroup D => f.1 o) := by
  intro f f' he
  obtain ⟨g,hg⟩ := f.2
  obtain ⟨g',hg'⟩ := f'.2
  apply Subtype.ext
  exact Equiv.ext (output_agreement D g f.1 g' f'.1 hq hg hg' o he).2

theorem outputGroup_card_le [Finite A] (hq : IsQuasigroup D) (o : A) :
    Nat.card (outputGroup D) ≤ Nat.card A :=
  Nat.card_le_card_of_injective _ (outputGroup_eval_injective D hq o)

/-- The free action partitions a finite carrier into orbits of the group order. -/
theorem outputGroup_card_dvd [Finite A] (hq : IsQuasigroup D) :
    Nat.card (outputGroup D) ∣ Nat.card A := by
  have stab (x : A) : MulAction.stabilizer (outputGroup D) x=⊥ := by
    ext f
    simp only [MulAction.mem_stabilizer_iff,Subgroup.mem_bot]
    constructor
    · intro hf
      exact outputGroup_eval_injective D hq x hf
    · rintro rfl
      rfl
  have he := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd stab)
  rw [Nat.card_prod] at he
  exact he.symm ▸ dvd_mul_left _ _

end Parastrophes.Eq917Image.SplitCandidate

namespace Parastrophes.Eq917Image.FrontProduct
open SandwichCandidate (U F)
variable {A : Type} (D : Magma A)
/-- The normalized a,b outputs admit the mixed-word pruning above. -/
theorem output_words_agree (a b : A ≃ A) (hq : IsQuasigroup D)
    (hb : ∀ x y, D.op (U D x) y=b (D.op x y))
    (hc : ∀ x y, D.op (a x) y=a (D.op (b x) y))
    (w v : List Bool) (o : A)
    (ho : SplitCandidate.word a b w o=SplitCandidate.word a b v o) :
    ∀ x, SplitCandidate.word a b w x=SplitCandidate.word a b v x := by
  apply SplitCandidate.word_output_agreement D (fun x => a (b.symm x)) a (U D) b hq _ hb w v o ho
  intro x y
  rw [hc,b.apply_symm_apply]
/-- The entire group generated by a and b has order dividing the carrier size. -/
theorem generated_outputs_card_dvd [Finite A] (h : Identity D)
    (a b : Equiv.Perm A)
    (hb : ∀ x y, D.op (U D x) y=b (D.op x y))
    (hc : ∀ x y, D.op (a x) y=a (D.op (b x) y)) :
    Nat.card (Subgroup.closure ({a,b} : Set (Equiv.Perm A))) ∣ Nat.card A := by
  have ha' : a ∈ SplitCandidate.outputGroup D := by
    refine ⟨b.symm.trans a,?_⟩
    intro x y
    change D.op (a (b.symm x)) y=a (D.op x y)
    rw [hc,b.apply_symm_apply]
  have hb' : b ∈ SplitCandidate.outputGroup D :=
    ⟨Equiv.ofBijective (U D) (unit_bijective D h),hb⟩
  have inc : Subgroup.closure ({a,b} : Set (Equiv.Perm A)) ≤ SplitCandidate.outputGroup D := by
    apply (Subgroup.closure_le _).mpr
    intro f hf
    rcases hf with rfl | hf
    · exact ha'
    · exact Set.mem_singleton_iff.mp hf ▸ hb'
  exact (Subgroup.card_dvd_of_le inc).trans
    (SplitCandidate.outputGroup_card_dvd D (quasigroup D h))

/-- If b is an involution and commutes with a, the unit is an involution
commuting with the input partner a∘b⁻¹, and cannot agree with it anywhere
unless a=b. These restrictions justify the Klein-four unit refinements. -/
theorem unit_partner_relations (a b : Equiv.Perm A) (hq : IsQuasigroup D)
    (hb : ∀ x y, D.op (U D x) y=b (D.op x y))
    (hc : ∀ x y, D.op (a x) y=a (D.op (b x) y))
    (b2 : ∀ x, b (b x)=x) (ab : Function.Commute a b) (hne : a ≠ b) :
    (∀ x, U D (U D x)=x) ∧
    Function.Commute (U D) (fun x => a (b.symm x)) ∧
    (∀ x, U D x ≠ a (b.symm x)) := by
  have hp (x y) : D.op (a (b.symm x)) y=a (D.op x y) := by
    rw [hc,b.apply_symm_apply]
  refine ⟨?_,?_,?_⟩
  · intro x
    apply (hq.2 x).1
    change D.op (U D (U D x)) x=D.op x x
    rw [hb,hb,b2]
  · intro x
    apply (hq.2 x).1
    change D.op (U D (a (b.symm x))) x=D.op (a (b.symm (U D x))) x
    rw [hb,hp,hp,hb,ab]
  · intro x he
    apply hne
    apply Equiv.ext
    intro t
    obtain ⟨y,rfl⟩ := (hq.1 x).2 t
    rw [← hp,← hb,he]

end Parastrophes.Eq917Image.FrontProduct
