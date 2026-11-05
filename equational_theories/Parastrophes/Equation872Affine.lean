import equational_theories.Parastrophes.Attributes
import equational_theories.Equations.All
import Mathlib.Algebra.Group.Hom.End
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel
import Mathlib.Data.Fin.VecNotation

/-!
# Affine E872 models have bounded row order

For `x*y = A(x)+B(y)+c` over an abelian group, E872 gives
`A+B²A=0` and `BA²+BAB+B³=1`. No commutation assumption is needed:
these relations imply `(B³-1)(B²+1)=0`, hence `B¹²=1`, and the translation
part of the twelfth iterate vanishes too, using `(1+B+B²+BA)(c)=0`.

This restriction is specific to affine models. A seven-element nonlinear
model below has a five-cycle through its zero row's diagonal.
-/
namespace Parastrophes.Eq872Affine

section Ring
variable {R : Type*} [Ring R] (a b : R)

theorem polynomial (h₁ : a + b*b*a = 0)
    (h₂ : b*a*a + b*a*b + b*b*b = 1) : (b^3-1)*(b^2+1) = 0 := by
  have hba : b*b*a = -a := eq_neg_of_add_eq_zero_right h₁
  have h : b*(b*a*a+b*a*b+b*b*b)=b := by simpa using congrArg (fun z => b*z) h₂
  have he : a*a+a*b = b^4-b := by
    have hh : b*(b*a*a+b*a*b+b*b*b) = (b*b*a)*a+(b*b*a)*b+b^4 := by
      noncomm_ring
    rw [hh, hba] at h
    apply (eq_sub_iff_add_eq).mpr
    calc
      a*a+a*b+b = a*a+a*b+((-a)*a+(-a)*b+b^4) := by rw [h]
      _ = b^4 := by noncomm_ring
  calc
    (b^3-1)*(b^2+1) = b*(b^4-b)+b*b*b-1 := by noncomm_ring
    _ = b*(a*a+a*b)+b*b*b-1 := by rw [he]
    _ = (b*a*a+b*a*b+b*b*b)-1 := by noncomm_ring
    _ = 0 := by rw [h₂]; simp

theorem power_twelve (h₁ : a + b*b*a = 0)
    (h₂ : b*a*a + b*a*b + b*b*b = 1) : b^12 = 1 := by
  have hp := polynomial a b h₁ h₂
  have he : b^12-1 = ((b^3-1)*(b^2+1))*(b^7-b^5+b^4+b^3-b^2+1) := by
    noncomm_ring
  rw [hp, zero_mul] at he
  exact sub_eq_zero.mp he

theorem sum_mul (h₁ : a + b*b*a = 0) :
    (∑ i ∈ Finset.range 12, b^i)*a = 0 := by
  have he : (∑ i ∈ Finset.range 12, b^i)*a =
      (1+b)*(1+b^4+b^8)*(a+b*b*a) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    noncomm_ring
  rw [he, h₁, mul_zero]

/-- The constant term is controlled by the same geometric sum. -/
theorem sum_factor (h₁ : a+b*b*a=0) :
    (∑ i ∈ Finset.range 12, b^i) =
      (b^7-b^5+b^4+b^3-b^2+1)*(1+b^2)*(1+b+b^2+b*a) := by
  have he : (∑ i ∈ Finset.range 12, b^i) =
      (b^7-b^5+b^4+b^3-b^2+1)*
        ((1+b^2)*(1+b+b^2+b*a)-b*(a+b*b*a)) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    noncomm_ring
  rw [he, h₁, mul_zero, sub_zero, mul_assoc]

end Ring

variable {G : Type} [AddCommGroup G] (A B : AddMonoid.End G)

@[implicit_reducible] def magma : Magma G := ⟨fun x y => A x + B y⟩

theorem coefficients (h : @Equation872 G (magma A B)) :
    A+B*B*A=0 ∧ B*A*A+B*A*B+B*B*B=1 := by
  constructor
  · apply AddMonoidHom.ext; intro y
    have he := h 0 y
    change A y+B (B (A y))=0
    change 0=A y+B (A (A 0+B 0)+B (A y+B 0)) at he
    simpa using he.symm
  · apply AddMonoidHom.ext; intro x
    have he := h x 0
    change B (A (A x))+B (A (B x))+B (B (B x))=x
    change x=A 0+B (A (A x+B x)+B (A 0+B x)) at he
    simpa [map_add, add_assoc] using he.symm

theorem linear_part_period (h : @Equation872 G (magma A B)) : B^12=1 :=
  power_twelve A B (coefficients A B h).1 (coefficients A B h).2

theorem row_iterate (x y : G) (n : Nat) :
    ((magma A B).op x)^[n] y =
      (∑ i ∈ Finset.range n, B^i) (A x) + (B^n) y := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs : (∑ i ∈ Finset.range (n+1), B^i) =
        1+B*(∑ i ∈ Finset.range n, B^i) := by
      rw [Finset.sum_range_succ']
      simp [pow_succ', Finset.mul_sum, add_comm]
    rw [Function.iterate_succ_apply', ih, hs, pow_succ']
    change A x+B ((∑ i ∈ Finset.range n, B^i) (A x)+(B^n) y) =
      (A x+B ((∑ i ∈ Finset.range n, B^i) (A x)))+B ((B^n) y)
    rw [map_add, add_assoc]

/-- Every row has order dividing twelve, on arbitrary carriers. -/
theorem row_period (h : @Equation872 G (magma A B)) (x y : G) :
    ((magma A B).op x)^[12] y = y := by
  rw [row_iterate, linear_part_period A B h]
  have hz := congrArg (fun f : AddMonoid.End G => f x)
    (sum_mul A B (coefficients A B h).1)
  simpa using hz

@[implicit_reducible] def affine (c : G) : Magma G := ⟨fun x y => A x+B y+c⟩

theorem affine_coefficients (c : G) (h : @Equation872 G (affine A B c)) :
    A+B*B*A=0 ∧ B*A*A+B*A*B+B*B*B=1 ∧ (1+B+B^2+B*A : AddMonoid.End G) c=0 := by
  have h0 := h 0 0
  change 0=A 0+B (A (A 0+B 0+c)+B (A 0+B 0+c)+c)+c at h0
  simp only [map_zero, zero_add, map_add, add_zero] at h0
  constructor
  · apply AddMonoidHom.ext; intro y
    change A y+B (B (A y))=0
    have hy := h 0 y
    change 0=A y+B (A (A 0+B 0+c)+B (A y+B 0+c)+c)+c at hy
    have he : (A y+B (B (A y)))+(B (A c)+B (B c)+B c+c)=0 := by
      simpa [map_add, add_assoc, add_left_comm, add_comm] using hy.symm
    rw [← h0, add_zero] at he
    exact he
  constructor
  · apply AddMonoidHom.ext; intro x
    change B (A (A x))+B (A (B x))+B (B (B x))=x
    have hx := h x 0
    change x=A 0+B (A (A x+B x+c)+B (A 0+B x+c)+c)+c at hx
    have he : (B (A (A x))+B (A (B x))+B (B (B x)))+
        (B (A c)+B (B c)+B c+c)=x := by
      simpa [map_add, add_assoc, add_left_comm, add_comm] using hx.symm
    rw [← h0, add_zero] at he
    exact he
  · change c+B c+B (B c)+B (A c)=0
    simpa [add_assoc, add_left_comm, add_comm] using h0.symm

/-- This includes a constant term and does not assume finite dimension,
a finite carrier, or commuting coefficient maps. -/
theorem affine_row_period (c : G) (h : @Equation872 G (affine A B c)) (x y : G) :
    ((affine A B c).op x)^[12] y=y := by
  obtain ⟨hA,hB,hc⟩ := affine_coefficients A B c h
  have hf : (affine A B c).op x=(magma 1 B).op (A x+c) := by
    funext y
    change A x+B y+c=(A x+c)+B y
    abel
  rw [hf, row_iterate, power_twelve A B hA hB]
  have hax : (∑ i ∈ Finset.range 12, B^i) (A x)=0 :=
    congrArg (fun f : AddMonoid.End G => f x) (sum_mul A B hA)
  have hcx : (∑ i ∈ Finset.range 12, B^i) c=0 := by
    rw [sum_factor A B hA]
    change (B^7-B^5+B^4+B^3-B^2+1 : AddMonoid.End G)
      ((1+B^2 : AddMonoid.End G) ((1+B+B^2+B*A : AddMonoid.End G) c))=0
    rw [hc, map_zero, map_zero]
  change (∑ i ∈ Finset.range 12, B^i) (A x+c)+y=y
  rw [map_add, hax, hcx, zero_add, zero_add]

/-- A source model whose zero row cycles through `0,1,2,3,4`. -/
@[implicit_reducible] def countermodel : Magma (Fin 7) := ⟨fun x y =>
  ![![1,2,3,4,0,5,6], ![0,4,2,3,6,1,5], ![0,3,2,1,4,5,6],
    ![0,1,4,3,2,5,6], ![2,1,0,3,5,4,6], ![3,6,2,0,4,5,1],
    ![3,5,2,0,1,6,4]] x y⟩

theorem countermodel_law : @Equation872 (Fin 7) countermodel := by decide

theorem countermodel_rows : IsSideQuasigroup .left countermodel := by
  unfold IsSideQuasigroup Function.Bijective Function.Injective Function.Surjective
  decide

theorem countermodel_five_cycle : (countermodel.op 0)^[5] 0=0 := by decide

theorem countermodel_not_period_twelve : (countermodel.op 0)^[12] 0 ≠ 0 := by decide

/-- No change of labels or abelian group structure makes this model affine. -/
theorem countermodel_not_affine (e : Fin 7 ≃ G) (c : G) :
    ¬ ∀ x y, e (countermodel.op x y)=A (e x)+B (e y)+c := by
  intro he
  have hf (x y : Fin 7) : (affine A B c).op (e x) (e y)=e (countermodel.op x y) :=
    (he x y).symm
  have hL : @Equation872 G (affine A B c) := by
    intro x y
    obtain ⟨x,rfl⟩ := e.surjective x
    obtain ⟨y,rfl⟩ := e.surjective y
    simp only [hf]
    exact congrArg e (countermodel_law x y)
  have hi (n : Nat) : e ((countermodel.op 0)^[n] 0)=
      ((affine A B c).op (e 0))^[n] (e 0) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih, hf]
  exact countermodel_not_period_twelve
    (e.injective ((hi 12).trans (affine_row_period A B c hL (e 0) (e 0))))

end Parastrophes.Eq872Affine
