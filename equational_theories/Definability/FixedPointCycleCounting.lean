import equational_theories.Definability.CloneFamilyCounting

/-!
Operations on a cyclic orbit together with one fixed point. The fixed point
multiplied by itself is fixed, and simultaneous cyclic shifts commute with the
operation. One output and one row determine every operation in this clone family.
-/

namespace Magma.FixedPointCycle

abbrev A (n : ℕ) := Option (ZMod n)
abbrev P (n : ℕ) := A n × (A n → A n)
variable {n : ℕ}

def shift (d : ZMod n) : A n → A n := Option.map (d + ·)
@[simp] theorem shift_none (d : ZMod n) : shift d none = none := rfl
@[simp] theorem shift_some (d x : ZMod n) : shift d (some x) = some (d + x) := rfl
@[simp] theorem shift_zero (x : A n) : shift 0 x = x := by cases x <;> simp [shift]
theorem shift_add (d e : ZMod n) (x : A n) : shift (d + e) x = shift d (shift e x) := by
  cases x <;> simp [shift, add_assoc]
@[simp] theorem shift_neg (d : ZMod n) (x : A n) : shift d (shift (-d) x) = x := by
  rw [← shift_add, add_neg_cancel, shift_zero]

def op (p : P n) : A n → A n → A n
  | none, none => none
  | none, some y => shift y p.1
  | some x, y => shift x (p.2 (shift (-x) y))

def extract (f : A n → A n → A n) : P n :=
  (f none (some 0), fun y => f (some 0) y)

@[simp] theorem extract_op (p : P n) : extract (op p) = p := by
  rcases p with ⟨c, f⟩
  simp [extract, op]

theorem op_injective : Function.Injective (op (n := n)) := by
  intro p q h
  simpa using congrArg extract h

theorem op_shift (p : P n) (d : ZMod n) (x y : A n) :
    op p (shift d x) (shift d y) = shift d (op p x y) := by
  cases x with
  | none => cases y <;> simp [op, shift_add]
  | some x =>
    simp only [shift_some, op]
    have he : -(d + x) + d = -x := by ring
    rw [← shift_add (-(d + x)), he, shift_add]

theorem op_extract (f : A n → A n → A n) (hzero : f none none = none)
    (hs : ∀ d x y, f (shift d x) (shift d y) = shift d (f x y)) :
    op (extract f) = f := by
  funext x y
  cases x with
  | none =>
    cases y with
    | none => exact hzero.symm
    | some y => simpa [op, extract] using (hs y none (some 0)).symm
  | some x => simpa [op, extract] using (hs x (some 0) (shift (-x) y)).symm

def fst : P n := (none, fun _ => some 0)
def snd : P n := (some 0, id)
def comp (p q r : P n) : P n := extract (fun x y => op p (op q x y) (op r x y))

theorem op_fst (x y : A n) : op fst x y = x := by
  cases x <;> cases y <;> simp [op, fst]
theorem op_snd (x y : A n) : op snd x y = y := by
  cases x <;> cases y <;> simp [op, snd]
theorem op_comp (p q r : P n) (x y : A n) :
    op (comp p q r) x y = op p (op q x y) (op r x y) := by
  have h := op_extract (fun x y => op p (op q x y) (op r x y)) rfl (by
    intro d x y
    dsimp only
    rw [op_shift, op_shift, op_shift])
  exact congrFun (congrFun h x) y

end Magma.FixedPointCycle

/-- info: 'Magma.FixedPointCycle.op_comp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.FixedPointCycle.op_comp
