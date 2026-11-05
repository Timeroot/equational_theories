import equational_theories.Equations.All
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
/-!
# A limitation of scalar affine E1112 image obstructions

Write a prospective division as `D(x,y)=p*x+q*y` over a field, with `q ≠ 0`.
Its original multiplication is `M(x,y)=(y-p*x)/q`. If M satisfies E1112,
then q has an inverse given by a fixed polynomial with integer coefficients.
Consequently an integral family of these commuting coefficients cannot lose
invertibility under reduction: the polynomial inverse reduces with it.

This recovers coefficients using the ambient ring operations. It does not
supply a magma term recovering M from D, and closes no characterization cell.
-/
namespace Parastrophes.Eq1112Affine
variable {K : Type} [Field K]
@[implicit_reducible] def source (p q : K) : Magma K := ⟨fun x y => (y-p*x)/q⟩
theorem coefficients (p q : K) (hq : q ≠ 0) (h : @Equation1112 K (source p q)) :
    p^2+q^2=q^4 ∧ p*(q^3-p*q+1)=0 := by
  constructor
  · have he := h 1 0
    change (1 : K) = (((1-p*(((0-p*1)/q-p*0)/q))/q)-p*0)/q at he
    field_simp [hq] at he
    linear_combination -he
  · have he := h 0 1
    change (0 : K) = (((0-p*(((1-p*0)/q-p*1)/q))/q)-p*1)/q at he
    field_simp [hq] at he
    linear_combination he

/-- A polynomial inverse for the right coefficient of division. -/
theorem inverse_polynomial (p q : K) (hq : q ≠ 0)
    (hA : p^2+q^2=q^4) (hB : p*(q^3-p*q+1)=0) :
    q*(q^5+2*q^4-q^3-2*q^2+q)=1 := by
  have he : q^2*(q*(q^5+2*q^4-q^3-2*q^2+q)-1)=0 := by
    linear_combination (p*(q^3+1)+q^5-q^3)*hB +
      (q*(p*(q^3+1)+q^5-q^3)-(q^3+1)^2)*hA
  have hz := (mul_eq_zero.mp he).resolve_left (pow_ne_zero 2 hq)
  exact sub_eq_zero.mp hz
/-- All coefficients of the source can be recovered polynomially from p and q.
The multiplication and subtraction here are those of K, not of the magma. -/
theorem source_via_polynomial (p q : K) (hq : q ≠ 0)
    (h : @Equation1112 K (source p q)) (x y : K) :
    (source p q).op x y = (q^5+2*q^4-q^3-2*q^2+q)*(y-p*x) := by
  obtain ⟨hA,hB⟩ := coefficients p q hq h
  have hi : q^5+2*q^4-q^3-2*q^2+q = q⁻¹ := by
    apply mul_left_cancel₀ hq
    rw [inverse_polynomial p q hq hA hB, mul_inv_cancel₀ hq]
  change (y-p*x)/q = _
  rw [hi, div_eq_mul_inv, mul_comm]

end Parastrophes.Eq1112Affine
