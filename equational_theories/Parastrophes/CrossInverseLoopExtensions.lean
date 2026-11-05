import equational_theories.Parastrophes.Equation481ImageBasis
import Mathlib.Tactic.Abel
import Mathlib.Data.Finite.Prod

/-!
# Central extensions of cross-inverse loops and E481 division images

A loop Q with right-inverse permutation J is cross-inverse when
`(x * y) * J(x) = y`. Its Cartesian square supplies an E481 division image:
`D((a,b),(c,d)) = (a*d, b*J(c))`. This works because D has a right identity
and `D(x,D(y,x)) = (y₂,J(y₁))`.

This module proves a way to enlarge the underlying loop without large tables.
For an abelian group K, put `(x,u)*(y,v)=(x*y,u+v+c(x,y))`. The required
conditions on the offsets are `c(e,x)=c(x,e)=0` and
`c(x,y)+c(x*y,J(x))=c(x,J(x))`. The lifted inverse is
`(J(x),-u-c(x,J(x)))`. Thus the construction can be iterated.

The resulting finite models are witnesses in the existing exact two-equation
image class. This does not settle its single-equation characterization.
-/

namespace Parastrophes.CrossInverseLoopExtensions

structure CIPLoop (A : Type) where
  magma : Magma A
  unit : A
  inverse : A ≃ A
  quasigroup : IsQuasigroup magma
  unit_left (x : A) : magma.op unit x = x
  unit_right (x : A) : magma.op x unit = x
  cross (x y : A) : magma.op (magma.op x y) (inverse x) = y

namespace CIPLoop
variable {A : Type} (Q : CIPLoop A)

theorem inverse_unit : Q.inverse Q.unit = Q.unit := by
  have h := Q.cross Q.unit Q.unit
  simpa only [Q.unit_left] using h

theorem cross_left (x y : A) :
    Q.magma.op x (Q.magma.op y (Q.inverse x)) = y := by
  apply (Q.quasigroup.2 (Q.inverse x)).1
  exact Q.cross x (Q.magma.op y (Q.inverse x))

/-- Three rotations of a multiplication triple apply J to all three entries. -/
theorem inverse_mul (x y : A) :
    Q.inverse (Q.magma.op x y) = Q.magma.op (Q.inverse x) (Q.inverse y) := by
  have h := Q.cross (Q.magma.op x y) (Q.inverse x)
  rw [Q.cross x y] at h
  have hh := Q.cross y (Q.inverse (Q.magma.op x y))
  rw [h] at hh
  exact hh.symm

/-- A central extension is specified by equations on the base alone. -/
structure Offset (K : Type) [AddCommGroup K] where
  value : A → A → K
  unit_left (x) : value Q.unit x = 0
  unit_right (x) : value x Q.unit = 0
  cross (x y) : value x y + value (Q.magma.op x y) (Q.inverse x) =
    value x (Q.inverse x)

variable {K : Type} [AddCommGroup K] (c : Q.Offset K)

@[implicit_reducible] def liftMagma : Magma (A × K) :=
  ⟨fun x y => (Q.magma.op x.1 y.1, x.2 + y.2 + c.value x.1 y.1)⟩

def liftInverse : (A × K) ≃ (A × K) where
  toFun x := (Q.inverse x.1, -x.2 - c.value x.1 (Q.inverse x.1))
  invFun y := (Q.inverse.symm y.1, -y.2 - c.value (Q.inverse.symm y.1) y.1)
  left_inv x := by
    apply Prod.ext
    · exact Q.inverse.symm_apply_apply x.1
    · simp only [Q.inverse.symm_apply_apply]
      abel
  right_inv y := by
    apply Prod.ext
    · exact Q.inverse.apply_symm_apply y.1
    · simp only [Q.inverse.apply_symm_apply]
      abel

theorem lift_quasigroup : IsQuasigroup (Q.liftMagma c) := by
  constructor
  · intro x
    constructor
    · intro y z h
      have h₁ := (Q.quasigroup.1 x.1).1 (congrArg Prod.fst h)
      have h₂ := congrArg Prod.snd h
      change x.2 + y.2 + c.value x.1 y.1 = x.2 + z.2 + c.value x.1 z.1 at h₂
      rw [h₁] at h₂
      exact Prod.ext h₁ (add_left_cancel (add_right_cancel h₂))
    · intro y
      obtain ⟨z, hz⟩ := (Q.quasigroup.1 x.1).2 y.1
      refine ⟨(z, y.2 - x.2 - c.value x.1 z), Prod.ext hz ?_⟩
      change x.2 + (y.2 - x.2 - c.value x.1 z) + c.value x.1 z = y.2
      abel
  · intro y
    constructor
    · intro x z h
      have h₁ := (Q.quasigroup.2 y.1).1 (congrArg Prod.fst h)
      have h₂ := congrArg Prod.snd h
      change x.2 + y.2 + c.value x.1 y.1 = z.2 + y.2 + c.value z.1 y.1 at h₂
      rw [h₁] at h₂
      exact Prod.ext h₁ (add_right_cancel (add_right_cancel h₂))
    · intro x
      obtain ⟨z, hz⟩ := (Q.quasigroup.2 y.1).2 x.1
      refine ⟨(z, x.2 - y.2 - c.value z y.1), Prod.ext hz ?_⟩
      change (x.2 - y.2 - c.value z y.1) + y.2 + c.value z y.1 = x.2
      abel

theorem lift_cross (x y : A × K) :
    (Q.liftMagma c).op ((Q.liftMagma c).op x y) (Q.liftInverse c x) = y := by
  apply Prod.ext
  · exact Q.cross x.1 y.1
  · change (x.2 + y.2 + c.value x.1 y.1) +
      (-x.2 - c.value x.1 (Q.inverse x.1)) +
      c.value (Q.magma.op x.1 y.1) (Q.inverse x.1) = y.2
    have hc := c.cross x.1 y.1
    calc
      _ = y.2 + (c.value x.1 y.1 +
          c.value (Q.magma.op x.1 y.1) (Q.inverse x.1) -
          c.value x.1 (Q.inverse x.1)) := by abel
      _ = y.2 := by rw [hc, sub_self, add_zero]

/-- The output is another loop of the same type, so successive extensions
need only supply another base offset certificate. -/
def extend : CIPLoop (A × K) where
  magma := Q.liftMagma c
  unit := (Q.unit, 0)
  inverse := Q.liftInverse c
  quasigroup := Q.lift_quasigroup c
  unit_left x := by
    apply Prod.ext
    · exact Q.unit_left x.1
    · change 0 + x.2 + c.value Q.unit x.1 = x.2
      rw [c.unit_left, zero_add, add_zero]
  unit_right x := by
    apply Prod.ext
    · exact Q.unit_right x.1
    · change x.2 + 0 + c.value x.1 Q.unit = x.2
      rw [c.unit_right, add_zero, add_zero]
  cross := Q.lift_cross c

@[implicit_reducible] def division : Magma (A × A) :=
  ⟨fun x y => (Q.magma.op x.1 y.2, Q.magma.op x.2 (Q.inverse y.1))⟩

def turn (x : A × A) : A × A := (x.2, Q.inverse x.1)

theorem division_unit (x : A × A) :
    Q.division.op x (Q.unit, Q.unit) = x := by
  apply Prod.ext
  · exact Q.unit_right x.1
  · change Q.magma.op x.2 (Q.inverse Q.unit) = x.2
    rw [Q.inverse_unit, Q.unit_right]

theorem division_turn (x : A × A) :
    Q.division.op (Q.unit, Q.unit) x = Q.turn x := by
  apply Prod.ext <;> exact Q.unit_left _

theorem division_cross (x y : A × A) :
    Q.division.op x (Q.division.op y x) = Q.turn y := by
  apply Prod.ext
  · exact Q.cross_left x.1 y.2
  · change Q.magma.op x.2 (Q.inverse (Q.magma.op y.1 x.2)) = Q.inverse y.1
    rw [Q.inverse_mul, Q.cross_left]

/-- The existing two-equation basis is satisfied without a finiteness
assumption. Finiteness is used only in its already-proved exact converse. -/
theorem division_basis : Eq481Image.Basis Q.division := by
  have hc (y : A × A) : Eq481Image.core Q.division y = (Q.unit, Q.unit) := by
    change Q.division.op y (Q.division.op y (Q.division.op y y)) = _
    rw [Q.division_cross, ← Q.division_turn, Q.division_cross]
    exact Prod.ext rfl Q.inverse_unit
  constructor
  · intro x y
    rw [hc, Q.division_unit]
  · intro x y z
    rw [Q.division_cross, Q.division_cross]

theorem division_inImage [Finite A] : InImage Law481 .left Q.division :=
  (Eq481Image.characterizes_fin Q.division).mp Q.division_basis

end CIPLoop

/-- Every finite right-unital crossed magma is an isotope of a cross-inverse
loop. The twisting automorphism f is a square root of the loop's inverse map.
This identifies the extra structure that a single-equation characterization
would have to recover; it does not assume that f⁻¹ is a uniform magma term. -/
theorem normalize {A : Type} [Finite A] (M : Magma A) (e : A)
    (unit : ∀ x, M.op x e = x)
    (cross : ∀ x y, M.op x (M.op y x) = M.op e y) :
    ∃ (Q : CIPLoop A) (f : A ≃ A), Q.unit = e ∧ Q.inverse = f.trans f ∧
      (∀ x y, Q.magma.op x (f y) = M.op x y) ∧
      (∀ x y, f (Q.magma.op x y) = Q.magma.op (f x) (f y)) := by
  classical
  have hq := FiniteCrossedIdentity.quasigroup M e unit cross
  let f := Equiv.ofBijective (M.op e) (hq.1 e)
  have fe : f e = e := unit e
  have fie : f.symm e = e := by
    apply f.injective
    rw [f.apply_symm_apply, fe]
  have rotate (x y : A) : M.op (M.op x y) (f x) = f y := by
    simpa only [cross y x] using cross (M.op x y) y
  have endo (x y : A) : f (M.op x y) = M.op (f x) (f y) := by
    have h := rotate y (M.op x y)
    rw [cross y x] at h
    exact h.symm
  let Q : CIPLoop A := {
    magma := ⟨fun x y => M.op x (f.symm y)⟩
    unit := e
    inverse := f.trans f
    quasigroup := ⟨fun x => (hq.1 x).comp f.symm.bijective,
      fun y => hq.2 (f.symm y)⟩
    unit_left := fun x => f.apply_symm_apply x
    unit_right := fun x => by
      change M.op x (f.symm e) = x
      rw [fie, unit]
    cross := fun x y => by
      change M.op (M.op x (f.symm y)) (f.symm (f (f x))) = y
      rw [f.symm_apply_apply, rotate, f.apply_symm_apply] }
  refine ⟨Q, f, rfl, rfl, ?_, ?_⟩
  · intro x y
    change M.op x (f.symm (f y)) = M.op x y
    rw [f.symm_apply_apply]
  · intro x y
    change f (M.op x (f.symm y)) = M.op (f x) (f.symm (f y))
    rw [endo, f.apply_symm_apply, f.symm_apply_apply]

end Parastrophes.CrossInverseLoopExtensions
