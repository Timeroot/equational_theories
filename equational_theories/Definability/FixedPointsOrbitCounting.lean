import equational_theories.Definability.CloneFamilyCounting

/-! A cyclic orbit and any inhabited set of fixed points. -/
namespace Magma.FixedPointsOrbit
abbrev A (K : Type) (n : ℕ) := K ⊕ ZMod n
abbrev P (K : Type) (n : ℕ) := (K → K → K) × (K → A K n) × (A K n → A K n)
variable {K : Type} {n : ℕ}
def shift (d : ZMod n) : A K n → A K n := Sum.map id (d + ·)
@[simp] theorem shift_inl (d : ZMod n) (i : K) : shift d (Sum.inl i) = Sum.inl i := rfl
@[simp] theorem shift_inr (d x : ZMod n) : shift d (Sum.inr x : A K n) = Sum.inr (d + x) := rfl
@[simp] theorem shift_zero (x : A K n) : shift 0 x = x := by cases x <;> simp [shift]
theorem shift_add (d e : ZMod n) (x : A K n) : shift (d + e) x = shift d (shift e x) := by
  cases x <;> simp [shift, add_assoc]
@[simp] theorem shift_neg (d : ZMod n) (x : A K n) : shift d (shift (-d) x) = x := by
  rw [← shift_add, add_neg_cancel, shift_zero]
def op (p : P K n) : A K n → A K n → A K n
  | .inl i, .inl j => .inl (p.1 i j)
  | .inl i, .inr y => shift y (p.2.1 i)
  | .inr x, y => shift x (p.2.2 (shift (-x) y))
variable [Inhabited K]

def extract (f : A K n → A K n → A K n) : P K n :=
  (fun i j => match f (.inl i) (.inl j) with | .inl k => k | .inr _ => default,
   fun i => f (.inl i) (.inr 0), fun y => f (.inr 0) y)
@[simp] theorem extract_op (p : P K n) : extract (op p) = p := by
  rcases p with ⟨a, b, c⟩
  simp [extract, op]
theorem op_injective : Function.Injective (op (K := K) (n := n)) := by
  intro p q h
  simpa using congrArg extract h
omit [Inhabited K] in
theorem op_shift (p : P K n) (d : ZMod n) (x y : A K n) :
    op p (shift d x) (shift d y) = shift d (op p x y) := by
  cases x with
  | inl i => cases y <;> simp [op, shift_add]
  | inr x =>
    simp only [shift_inr, op]
    have he : -(d + x) + d = -x := by ring
    rw [← shift_add (-(d + x)), he, shift_add]
theorem op_extract (f : A K n → A K n → A K n)
    (hf : ∀ i j, ∃ k, f (.inl i) (.inl j) = .inl k)
    (hs : ∀ d x y, f (shift d x) (shift d y) = shift d (f x y)) : op (extract f) = f := by
  funext x y
  cases x with
  | inl i =>
    cases y with
    | inl j => obtain ⟨k, hk⟩ := hf i j; simp [op, extract, hk]
    | inr y => simpa [op, extract] using (hs y (.inl i) (.inr 0)).symm
  | inr x => simpa [op, extract] using (hs x (.inr 0) (shift (-x) y)).symm
def fst : P K n := (fun i _ => i, Sum.inl, fun _ => .inr 0)
def snd : P K n := (fun _ j => j, fun _ => .inr 0, id)
def comp (p q r : P K n) : P K n := extract (fun x y => op p (op q x y) (op r x y))
omit [Inhabited K] in
theorem op_fst (x y : A K n) : op fst x y = x := by
  cases x <;> cases y <;> simp [op, fst]
omit [Inhabited K] in
theorem op_snd (x y : A K n) : op snd x y = y := by
  cases x <;> cases y <;> simp [op, snd]
theorem op_comp (p q r : P K n) (x y : A K n) :
    op (comp p q r) x y = op p (op q x y) (op r x y) := by
  have h := op_extract (fun x y => op p (op q x y) (op r x y))
    (fun i j => ⟨p.1 (q.1 i j) (r.1 i j), rfl⟩) (by
      intro d x y
      dsimp only
      rw [op_shift, op_shift, op_shift])
  exact congrFun (congrFun h x) y
end Magma.FixedPointsOrbit

/-- info: 'Magma.FixedPointsOrbit.op_comp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.FixedPointsOrbit.op_comp
