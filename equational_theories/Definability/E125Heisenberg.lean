import equational_theories.Definability.E125Homogeneous
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.LinearCombination

/-!
# A homogeneous E125 magma with noncommuting unary translations

On the 343-element Heisenberg group over `ZMod 7`, define a triangular
permutation `f`. Two seven-case coefficient checks and symbolic linear
algebra prove `f (f ((f x)⁻¹) * f x) = x`. Hence
`x ◇ y = f (y*x⁻¹)*x` satisfies E125 and all right group translations
are automorphisms. The square and cube maps are left multiplication by
`f 1` and `f (f 1)`, which do not commute.

The coefficient functions were found by solving the linear cocycle
equations over `F₇`, requiring degree at most one under simultaneous
translation of the two base coordinates. No 343-by-343 table is stored
or checked. This refutes the homogeneous commutation conjecture; it is
not a new catalogue separation.
-/

namespace E125Heisenberg
abbrev K := ZMod 7

@[ext] structure H where
  c : K
  d : K
  e : K
  deriving DecidableEq, Fintype

def mul (x y : H) : H := ⟨x.c+y.c, x.d+y.d, x.e+y.e+x.d*y.c⟩
def inv (x : H) : H := ⟨-x.c,-x.d,-x.e+x.d*x.c⟩

instance : Group H where
  mul := mul
  one := ⟨0,0,0⟩
  inv := inv
  mul_assoc := by
    intro a b c
    change mul (mul a b) c = mul a (mul b c)
    ext <;> dsimp [mul] <;> ring
  one_mul := by
    intro a
    change mul ⟨0,0,0⟩ a = a
    ext <;> dsimp [mul] <;> ring
  mul_one := by
    intro a
    change mul a ⟨0,0,0⟩ = a
    ext <;> dsimp [mul] <;> ring
  inv_mul_cancel := by
    intro a
    change mul (inv a) a = ⟨0,0,0⟩
    ext <;> dsimp [mul,inv] <;> ring

def u (z : K) : K := 4*z+z^2+6*z^3+6*z^4+5*z^5
def v (z : K) : K := 5*z^2+3*z^4+z^6

def f (x : H) : H := ⟨4*x.c+1,4*x.d+v x.c,4*x.e+u x.c⟩

lemma v_condition (c : K) : 2*v c+4*v (-(4*c+1))+v (2*c+5)=0 := by
  revert c
  decide

lemma u_condition (c : K) :
    2*u c+4*u (-(4*c+1))+4*v (-(4*c+1))*(4*c+1)+u (2*c+5)=0 := by
  revert c
  decide

lemma functional_equation (x : H) : f (f (f x)⁻¹ * f x) = x := by
  rcases x with ⟨c,d,e⟩
  have h7 : (7 : K)=0 := by decide
  have hc : 4*(-(4*c+1))+1+(4*c+1)=2*c+5 := by
    linear_combination (-2*c-1)*h7
  change f (mul (f (inv (f ⟨c,d,e⟩))) (f ⟨c,d,e⟩)) = _
  dsimp only [f,mul,inv]
  rw [hc]
  apply H.ext
  · linear_combination c*h7+3*h7
  · linear_combination v_condition c - (7*d+2*v c)*h7
  · linear_combination u_condition c - (7*e+2*u c)*h7

@[reducible] def model : Magma H := ⟨E63Family.Homogeneous.op f⟩

lemma equation125 : @Equation125 H model :=
  (E63Family.Homogeneous.equation125_iff f).mpr functional_equation

lemma right_equivariant (x y z : H) : model.op (x*z) (y*z) = model.op x y*z :=
  E63Family.Homogeneous.right_equivariant f x y z

lemma unary_bijective (t : FreeMagma Unit) :
    Function.Bijective (fun x => @FreeMagma.evalInMagma Unit H model (fun _ => x) t) :=
  E63Family.Homogeneous.unary_term_bijective f t

lemma square_cube_not_commute : ¬ Commute (f 1) (f (f 1)) := by
  change f 1 * f (f 1) ≠ f (f 1) * f 1
  decide

def coordinates : H ≃ K × K × K where
  toFun x := (x.c,x.d,x.e)
  invFun x := ⟨x.1,x.2.1,x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma card : Fintype.card H = 343 := by
  rw [Fintype.card_congr coordinates, Fintype.card_prod, Fintype.card_prod]
  decide
end E125Heisenberg

spectrum_assert E125Heisenberg.equation125 complete
spectrum_assert E125Heisenberg.square_cube_not_commute complete
spectrum_assert E125Heisenberg.card complete
spectrum_assert E125Heisenberg.right_equivariant complete
spectrum_assert E125Heisenberg.unary_bijective complete
