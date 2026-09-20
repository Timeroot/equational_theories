import equational_theories.Definability.UnaryMapCounting

/-! Operations commuting with an entire family of unary maps form a clone family. -/
namespace Magma.UnaryMapFamily
variable {A I : Type}
abbrev P (u : I → A → A) := {f : A → A → A // ∀ i, UnaryMap.Commutes (u i) f}
def op {u : I → A → A} (p : P u) : A → A → A := p.val
def fst (u : I → A → A) : P u := ⟨fun x _ => x, fun _ _ _ => rfl⟩
def snd (u : I → A → A) : P u := ⟨fun _ y => y, fun _ _ _ => rfl⟩
def comp {u : I → A → A} (p q r : P u) : P u :=
  ⟨fun x y => op p (op q x y) (op r x y), by
    intro i x y
    change p.val (q.val (u i x) (u i y)) (r.val (u i x) (u i y)) = _
    rw [q.property i, r.property i, p.property i]
    rfl⟩
theorem op_injective (u : I → A → A) : Function.Injective (@op A I u) := Subtype.val_injective
theorem op_fst (u : I → A → A) (x y : A) : op (fst u) x y = x := rfl
theorem op_snd (u : I → A → A) (x y : A) : op (snd u) x y = y := rfl
theorem op_comp {u : I → A → A} (p q r : P u) (x y : A) :
    op (comp p q r) x y = op p (op q x y) (op r x y) := rfl
end Magma.UnaryMapFamily
