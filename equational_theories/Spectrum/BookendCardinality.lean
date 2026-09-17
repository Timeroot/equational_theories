import equational_theories.Spectrum.Basic
import equational_theories.Equations.All
import Mathlib.GroupTheory.Perm.Sign

/-!
# A parity obstruction for the bookend law E167

On ordered pairs, `T(x,y) = (x ◇ y, y ◇ x)` squares to the coordinate swap.
Consequently the swap must be an even permutation. For an eleven-element carrier
it is the product of 55 disjoint transpositions and hence odd. We compute only
the sign of this one fixed permutation, never enumerate magma operations.
-/

namespace Spectrum.Bookend

variable {G : Type*} [Magma G] (h : Equation167 G)
include h

def pairRoot : Equiv.Perm (G × G) where
  toFun p := (p.1 ◇ p.2, p.2 ◇ p.1)
  invFun p := (p.2 ◇ p.1, p.1 ◇ p.2)
  left_inv p := Prod.ext (h p.1 p.2).symm (h p.2 p.1).symm
  right_inv p := Prod.ext (h p.1 p.2).symm (h p.2 p.1).symm

theorem pairRoot_sq : pairRoot h * pairRoot h = Equiv.prodComm G G := by
  ext p <;> exact (h _ _).symm

theorem swap_even [Fintype G] [DecidableEq G] :
    Equiv.Perm.sign (Equiv.prodComm G G) = 1 := by
  rw [← pairRoot_sq h, Equiv.Perm.sign_mul]
  exact Int.units_mul_self _

end Bookend

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
theorem not_order_167_11 : ¬ Law167.HasModel 11 := by
  rintro ⟨M, hM⟩
  letI := M
  have he := Bookend.swap_even (Law167.models_iff.mp hM)
  have ho : Equiv.Perm.sign (Equiv.prodComm (Fin 11) (Fin 11)) ≠ 1 := by decide
  exact ho he

/-- info: 'Spectrum.not_order_167_11' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_order_167_11

end Spectrum
