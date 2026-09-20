import equational_theories.Definability.CloneFamilyCounting

/-! Binary operations preserving a relation of any finite arity form a clone
family. Counting source and target operations in that family obstructs mutual
term recovery, by `not_termStructuralFromFin_of_cloneFamily_count`. -/

namespace Magma.FiniteRelationCounting

variable {A I : Type}

def Compatible (R : (I → A) → Prop) (f : A → A → A) : Prop :=
  ∀ x y, R x → R y → R (fun i => f (x i) (y i))

instance [Fintype A] [Fintype I] [DecidableEq I] (R : (I → A) → Prop) [DecidablePred R]
    (f : A → A → A) : Decidable (Compatible R f) := by
  unfold Compatible
  infer_instance

abbrev P (R : (I → A) → Prop) := {f : A → A → A // Compatible R f}

def op {R : (I → A) → Prop} (p : P R) : A → A → A := p.val

def fst (R : (I → A) → Prop) : P R := ⟨fun x _ => x, fun _ _ hx _ => hx⟩

def snd (R : (I → A) → Prop) : P R := ⟨fun _ y => y, fun _ _ _ hy => hy⟩

def comp {R : (I → A) → Prop} (p q r : P R) : P R :=
  ⟨fun x y => op p (op q x y) (op r x y), fun x y hx hy =>
    p.property _ _ (q.property x y hx hy) (r.property x y hx hy)⟩

theorem op_injective (R : (I → A) → Prop) : Function.Injective (@op A I R) :=
  Subtype.val_injective

theorem op_fst (R : (I → A) → Prop) (x y : A) : op (fst R) x y = x := rfl

theorem op_snd (R : (I → A) → Prop) (x y : A) : op (snd R) x y = y := rfl

theorem op_comp {R : (I → A) → Prop} (p q r : P R) (x y : A) :
    op (comp p q r) x y = op p (op q x y) (op r x y) := rfl

end Magma.FiniteRelationCounting
