import equational_theories.Definability.CloneFamilyCounting

/-! Affine binary operations on the two-dimensional vector space over ZMod n.
The coefficient tuples form an injectively parametrized clone family. -/

namespace Magma.MatrixAffine

abbrev V (n : ℕ) := Fin 2 → ZMod n
abbrev M (n : ℕ) := Fin 2 → Fin 2 → ZMod n
abbrev P (n : ℕ) := M n × M n × V n

variable {n : ℕ}

def act (a : M n) (x : V n) : V n := fun i => a i 0 * x 0 + a i 1 * x 1
def op (p : P n) (x y : V n) : V n := act p.1 x + act p.2.1 y + p.2.2
def unit : M n := fun i j => if i = j then 1 else 0
def basis (j : Fin 2) : V n := fun i => if i = j then 1 else 0
def mul (a b : M n) : M n := fun i j => a i 0 * b 0 j + a i 1 * b 1 j
def comp (p q r : P n) : P n :=
  (mul p.1 q.1 + mul p.2.1 r.1,
   mul p.1 q.2.1 + mul p.2.1 r.2.1,
   act p.1 q.2.2 + act p.2.1 r.2.2 + p.2.2)

theorem op_injective : Function.Injective (op (n := n)) := by
  rintro ⟨a, b, c⟩ ⟨d, e, f⟩ h
  have hconst : c = f := by
    funext i
    have hi := congrFun (congrFun (congrFun h 0) 0) i
    simpa [op, act] using hi
  have ha : a = d := by
    funext i j
    have hi := congrFun (congrFun (congrFun h (basis j)) 0) i
    fin_cases j <;> simpa [op, act, basis, hconst] using hi
  have hb : b = e := by
    funext i j
    have hi := congrFun (congrFun (congrFun h 0) (basis j)) i
    fin_cases j <;> simpa [op, act, basis, hconst] using hi
  exact Prod.ext ha (Prod.ext hb hconst)

theorem op_fst (x y : V n) : op (unit, 0, 0) x y = x := by
  funext i
  fin_cases i <;> simp [op, act, unit]

theorem op_snd (x y : V n) : op (0, unit, 0) x y = y := by
  funext i
  fin_cases i <;> simp [op, act, unit]

theorem op_comp (p q r : P n) (x y : V n) :
    op (comp p q r) x y = op p (op q x y) (op r x y) := by
  funext i
  simp only [op, comp, act, mul, Pi.add_apply]
  ring

end Magma.MatrixAffine

/-- info: 'Magma.MatrixAffine.op_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.MatrixAffine.op_injective
/-- info: 'Magma.MatrixAffine.op_comp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.MatrixAffine.op_comp
