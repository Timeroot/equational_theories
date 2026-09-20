import equational_theories.Definability.CloneFamilyCounting

/-! Operations equivariant under simultaneous shifts of several free cyclic
orbits. A row with first cyclic coordinate zero parametrizes each input orbit. -/

namespace Magma.FreeOrbit
abbrev A (n k : ℕ) := ZMod n × Fin k
abbrev P (n k : ℕ) := Fin k → A n k → A n k
variable {n k : ℕ}
def shift (d : ZMod n) (x : A n k) : A n k := (d + x.1, x.2)
@[simp] theorem shift_zero (x : A n k) : shift 0 x = x := by simp [shift]
theorem shift_add (d e : ZMod n) (x : A n k) : shift (d + e) x = shift d (shift e x) := by
  simp [shift, add_assoc]
@[simp] theorem shift_neg (d : ZMod n) (x : A n k) : shift d (shift (-d) x) = x := by
  rw [← shift_add, add_neg_cancel, shift_zero]
def op (p : P n k) (x y : A n k) : A n k := shift x.1 (p x.2 (shift (-x.1) y))
def extract (f : A n k → A n k → A n k) : P n k := fun i y => f (0, i) y
@[simp] theorem extract_op (p : P n k) : extract (op p) = p := by funext i y; simp [extract, op]
theorem op_injective : Function.Injective (op (n := n) (k := k)) := by
  intro p q h
  simpa using congrArg extract h
theorem op_shift (p : P n k) (d : ZMod n) (x y : A n k) :
    op p (shift d x) (shift d y) = shift d (op p x y) := by
  change shift (d + x.1) (p x.2 (shift (-(d + x.1)) (shift d y))) = _
  have he : -(d + x.1) + d = -x.1 := by ring
  rw [← shift_add (-(d + x.1)), he, shift_add]
  rfl
theorem op_extract (f : A n k → A n k → A n k)
    (hs : ∀ d x y, f (shift d x) (shift d y) = shift d (f x y)) : op (extract f) = f := by
  funext x y
  have h := hs x.1 (0, x.2) (shift (-x.1) y)
  simpa [op, extract, shift] using h.symm
def fst : P n k := fun i _ => (0, i)
def snd : P n k := fun _ y => y
def comp (p q r : P n k) : P n k := extract (fun x y => op p (op q x y) (op r x y))
theorem op_fst (x y : A n k) : op fst x y = x := by simp [op, fst, shift]
theorem op_snd (x y : A n k) : op snd x y = y := by simp [op, snd]
theorem op_comp (p q r : P n k) (x y : A n k) :
    op (comp p q r) x y = op p (op q x y) (op r x y) := by
  have h := op_extract (fun x y => op p (op q x y) (op r x y)) (by
    intro d x y
    dsimp only
    rw [op_shift, op_shift, op_shift])
  exact congrFun (congrFun h x) y
end Magma.FreeOrbit

/-- info: 'Magma.FreeOrbit.op_comp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.FreeOrbit.op_comp
