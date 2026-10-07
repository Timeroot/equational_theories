import equational_theories.MagmaLaw
import equational_theories.Equations.Eqns1_999
import equational_theories.Spectrum.Status
import Mathlib.GroupTheory.OrderOfElement

/-!
# Homogeneous completion by unary term permutations

In a finite magma where every unary term operation is bijective, the unary
terms form a group under composition. Pointwise multiplication of two unary
term operations is another unary term operation, so it gives a magma on this
group. Every source law holds pointwise, evaluation is a homomorphism, and
right composition is a regular group of automorphisms.

This applies in particular to the E125 examples with bijective unary terms.
It explains how such finite examples yield homogeneous ones without assuming
an abelian group representation. No permutation group or table is enumerated.
-/

namespace UnaryHomogenization
variable {G : Type} [M : Magma G]

def unary (f : G → G) : Prop := ∃ t : FreeMagma Unit, ∀ x,
  @FreeMagma.evalInMagma Unit G M (fun _ => x) t = f x

lemma unary_id : unary (M := M) id := ⟨.Leaf (), fun _ => rfl⟩
lemma unary_comp {f g : G → G} (hf : unary (M := M) f) (hg : unary (M := M) g) :
    unary (M := M) (f ∘ g) := by
  obtain ⟨s,hs⟩ := hf
  obtain ⟨t,ht⟩ := hg
  refine ⟨FreeMagma.evalInMagma (fun _ => t) s, fun x => ?_⟩
  rw [FreeMagma.SubstEval]
  simpa only [Function.comp_def,ht] using hs (g x)
lemma unary_op {f g : G → G} (hf : unary (M := M) f) (hg : unary (M := M) g) :
    unary (M := M) (fun x => M.op (f x) (g x)) := by
  obtain ⟨s,hs⟩ := hf
  obtain ⟨t,ht⟩ := hg
  exact ⟨.Fork s t, fun x => by simp only [FreeMagma.evalInMagma,hs,ht]⟩

def unaryMonoid : Submonoid (Equiv.Perm G) where
  carrier := {e | unary (M := M) e}
  one_mem' := unary_id
  mul_mem' {a b} hf hg := by
    exact unary_comp (f := a) (g := b) hf hg

variable [Finite G]
def unaryGroup : Subgroup (Equiv.Perm G) := Subgroup.closure (unaryMonoid (M := M) : Set _)

lemma mem_unaryGroup (e : Equiv.Perm G) : e ∈ unaryGroup (M := M) ↔ unary (M := M) e := by
  have hh := Subgroup.closure_toSubmonoid_of_finite (s := (unaryMonoid (M := M) : Set (Equiv.Perm G)))
  rw [Submonoid.closure_eq] at hh
  exact SetLike.ext_iff.mp hh e

variable (hbij : ∀ t : FreeMagma Unit,
  Function.Bijective (fun x => @FreeMagma.evalInMagma Unit G M (fun _ => x) t))

@[reducible] noncomputable def model : Magma (unaryGroup (M := M)) where
  op p q := by
    have hu := unary_op ((mem_unaryGroup p.val).mp p.property) ((mem_unaryGroup q.val).mp q.property)
    have hb : Function.Bijective (fun x => M.op (p.val x) (q.val x)) := by
      obtain ⟨t,ht⟩ := hu
      have he : (fun x => @FreeMagma.evalInMagma Unit G M (fun _ => x) t) =
          (fun x => M.op (p.val x) (q.val x)) := funext ht
      exact he ▸ hbij t
    exact ⟨Equiv.ofBijective _ hb, (mem_unaryGroup _).mpr hu⟩

lemma op_apply (p q : unaryGroup (M := M)) (x : G) :
    ((model hbij).op p q).val x = M.op (p.val x) (q.val x) := rfl


/-- Evaluating at any source point is a magma homomorphism. -/
def evaluation (x : G) : @MagmaHom (unaryGroup (M := M)) G (model hbij) M := by
  letI := model hbij
  exact ⟨fun p => p.val x, fun _ _ => rfl⟩

lemma eval_apply {α : Type} (t : FreeMagma α) (v : α → unaryGroup (M := M)) (x : G) :
    (@FreeMagma.evalInMagma α _ (model hbij) v t).val x =
      @FreeMagma.evalInMagma α G M (fun a => (v a).val x) t := by
  induction t with
  | Leaf _ => rfl
  | Fork s t hs ht =>
    change M.op _ _ = M.op _ _
    rw [hs,ht]

/-- Every equational law of the source holds in its homogeneous completion. -/
lemma satisfies {α : Type} (L : Law.MagmaLaw α) (h : _root_.satisfies G L) :
    @_root_.satisfies α (unaryGroup (M := M)) (model hbij) L := by
  intro v
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change (@FreeMagma.evalInMagma α _ (model hbij) v L.lhs).val x =
    (@FreeMagma.evalInMagma α _ (model hbij) v L.rhs).val x
  rw [eval_apply,eval_apply]
  exact h _

lemma equation125 (h : Equation125 G) : @Equation125 (unaryGroup (M := M)) (model hbij) := by
  intro p q
  apply Subtype.ext
  apply Equiv.ext
  intro x
  exact h (p.val x) (q.val x)

lemma right_equivariant (p q r : unaryGroup (M := M)) :
    (model hbij).op (p*r) (q*r) = (model hbij).op p q*r := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  rfl
end UnaryHomogenization

spectrum_assert UnaryHomogenization.equation125 complete
spectrum_assert UnaryHomogenization.right_equivariant complete

spectrum_assert UnaryHomogenization.satisfies complete
