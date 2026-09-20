import equational_theories.Definability.RelationCounting

/-! Operations preserving a family of binary relations form a clone family. -/
namespace Magma.RelationFamilyCounting
variable {A I : Type}
abbrev P (R : I → A → A → Prop) :=
  {f : A → A → A // ∀ i, RelationCounting.Compatible (R i) f}
def op {R : I → A → A → Prop} (p : P R) : A → A → A := p.val
def fst (R : I → A → A → Prop) : P R := ⟨fun x _ => x, fun _ _ _ _ _ h _ => h⟩
def snd (R : I → A → A → Prop) : P R := ⟨fun _ y => y, fun _ _ _ _ _ _ h => h⟩
def comp {R : I → A → A → Prop} (p q r : P R) : P R :=
  ⟨fun x y => op p (op q x y) (op r x y), fun i x y z w hxy hzw =>
    p.property i _ _ _ _ (q.property i x y z w hxy hzw) (r.property i x y z w hxy hzw)⟩
theorem op_injective (R : I → A → A → Prop) : Function.Injective (@op A I R) := Subtype.val_injective
theorem op_fst (R : I → A → A → Prop) (x y : A) : op (fst R) x y = x := rfl
theorem op_snd (R : I → A → A → Prop) (x y : A) : op (snd R) x y = y := rfl
theorem op_comp {R : I → A → A → Prop} (p q r : P R) (x y : A) :
    op (comp p q r) x y = op p (op q x y) (op r x y) := rfl
end Magma.RelationFamilyCounting
