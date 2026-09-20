import equational_theories.Definability.CloneFamilyCounting

/-! Binary operations preserving a fixed binary relation form a clone family.
Counts within this family obstruct mutual term recovery. -/
namespace Magma.RelationCounting
variable {A : Type}
def Compatible (R : A → A → Prop) (f : A → A → A) : Prop :=
  ∀ x y z w, R x y → R z w → R (f x z) (f y w)
instance [Fintype A] (R : A → A → Prop) [DecidableRel R] (f : A → A → A) :
    Decidable (Compatible R f) := by unfold Compatible; infer_instance
abbrev P (R : A → A → Prop) := {f : A → A → A // Compatible R f}
def op {R : A → A → Prop} (p : P R) : A → A → A := p.val
def fst (R : A → A → Prop) : P R := ⟨fun x _ => x, fun _ _ _ _ h _ => h⟩
def snd (R : A → A → Prop) : P R := ⟨fun _ y => y, fun _ _ _ _ _ h => h⟩
def comp {R : A → A → Prop} (p q r : P R) : P R :=
  ⟨fun x y => op p (op q x y) (op r x y), fun x y z w hxy hzw =>
    p.property _ _ _ _ (q.property x y z w hxy hzw) (r.property x y z w hxy hzw)⟩
theorem op_injective (R : A → A → Prop) : Function.Injective (@op A R) := Subtype.val_injective
theorem op_fst (R : A → A → Prop) (x y : A) : op (fst R) x y = x := rfl
theorem op_snd (R : A → A → Prop) (x y : A) : op (snd R) x y = y := rfl
theorem op_comp {R : A → A → Prop} (p q r : P R) (x y : A) :
    op (comp p q r) x y = op p (op q x y) (op r x y) := rfl
end Magma.RelationCounting
