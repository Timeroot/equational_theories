import equational_theories.Definability.CloneFamilyCounting

/-!
# Counting operations commuting with cyclic translations

Every operation equivariant under simultaneous cyclic translations has the form
`x + f (y - x)`. These parameters are unique, contain both projections, and are
closed under term composition. Hence their model counts obstruct term recovery.
-/

namespace Magma.Translation

variable {n : ℕ}

def op (f : ZMod n → ZMod n) (x y : ZMod n) : ZMod n := x + f (y - x)
def comp (f g h : ZMod n → ZMod n) : ZMod n → ZMod n :=
  fun d => g d + f (h d - g d)

theorem op_injective : Function.Injective (op (n := n)) := by
  intro f g h
  funext d
  simpa [op] using congrFun (congrFun h 0) d

theorem op_fst (x y : ZMod n) : op (fun _ => 0) x y = x := by simp [op]
theorem op_snd (x y : ZMod n) : op id x y = y := by simp [op]

theorem op_comp (f g h : ZMod n → ZMod n) (x y : ZMod n) :
    op (comp f g h) x y = op f (op g x y) (op h x y) := by
  simp [op, comp, add_assoc]

end Magma.Translation

/-- info: 'Magma.Translation.op_comp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.Translation.op_comp
