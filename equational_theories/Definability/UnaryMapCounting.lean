import equational_theories.Definability.CloneFamilyCounting

/-! Operations commuting with a fixed unary map form a clone family.
The map need not be invertible. Counting its compatible source and target
operations therefore obstructs mutual term recovery. -/

namespace Magma.UnaryMap
variable {A : Type}

def Commutes (u : A → A) (f : A → A → A) : Prop :=
  ∀ x y, f (u x) (u y) = u (f x y)
instance [Fintype A] [DecidableEq A] (u : A → A) (f : A → A → A) :
    Decidable (Commutes u f) := by unfold Commutes; infer_instance
abbrev P (u : A → A) := {f : A → A → A // Commutes u f}
def op {u : A → A} (p : P u) : A → A → A := p.val
def fst (u : A → A) : P u := ⟨fun x _ => x, fun _ _ => rfl⟩
def snd (u : A → A) : P u := ⟨fun _ y => y, fun _ _ => rfl⟩
def comp {u : A → A} (p q r : P u) : P u :=
  ⟨fun x y => op p (op q x y) (op r x y), by
    intro x y
    change p.val (q.val (u x) (u y)) (r.val (u x) (u y)) = _
    rw [q.property, r.property, p.property]
    rfl⟩
theorem op_injective (u : A → A) : Function.Injective (@op A u) := Subtype.val_injective
theorem op_fst (u : A → A) (x y : A) : op (fst u) x y = x := rfl
theorem op_snd (u : A → A) (x y : A) : op (snd u) x y = y := rfl
theorem op_comp {u : A → A} (p q r : P u) (x y : A) :
    op (comp p q r) x y = op p (op q x y) (op r x y) := rfl
end Magma.UnaryMap
